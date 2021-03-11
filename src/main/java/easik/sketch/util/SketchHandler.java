package easik.sketch.util;

//~--- non-JDK imports --------------------------------------------------------

//~--- JDK imports ------------------------------------------------------------
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import javax.swing.JOptionPane;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

import easik.DocumentInfo;
import easik.Easik;
import easik.EasikConstants;
import easik.database.types.EasikType;
import easik.model.attribute.EntityAttribute;
import easik.model.constraint.CommutativeDiagram;
import easik.model.constraint.ConstraintException;
import easik.model.constraint.EqualizerConstraint;
import easik.model.constraint.LimitConstraint;
import easik.model.constraint.ModelConstraint;
import easik.model.constraint.ProductConstraint;
import easik.model.constraint.PullbackConstraint;
import easik.model.constraint.SumConstraint;
import easik.model.keys.UniqueIndexable;
import easik.model.keys.UniqueKey;
import easik.model.path.ModelPath;
import easik.sketch.Sketch;
import easik.sketch.edge.InjectiveEdge;
import easik.sketch.edge.NormalEdge;
import easik.sketch.edge.PartialEdge;
import easik.sketch.edge.SketchEdge;
import easik.sketch.util.graph.SketchGraphModel;
import easik.sketch.vertex.EntityNode;
import easik.ui.SketchFrame;

/**
 * The SketchHandler is the overloaded handler for reading the sketches in from
 * XML. There is very little error checking in here to deal with bad XML.
 *
 * This handler will read XML both when importing a sketch into an overview
 *
 * TODO: Implement schema checking
 *
 * @author Rob Fletcher 2005
 * @author Kevin Green 2006
 * @author Vera Ranieri 2006
 * @version 2006-07-14 Vera Ranieri
 */
public class SketchHandler extends DefaultHandler {
  /** The x-position of the current constraint being defined */
  private int _curConstraintX = 0;

  /** The y-position of the current constraint being defined */
  private int _curConstraintY = 0;

  /** The visibility of the current constraint */
  private boolean _curConstraintVisible = true;

  /** Whether all constraints are visible */
  private boolean _allConstraintsVisible;

  /** The paths of the sketch, indexed by name */
  private LinkedHashMap<String, ModelPath<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge>> _allPaths;

  /** The current connection parameters */
  private HashMap<String, String> _connParams;

  /** The constraints of the sketch */
  private LinkedList<ModelConstraint<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge>> _constraints;

  /** The paths involved in the current constraint being defined */
  private ArrayList<ModelPath<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge>> _curConstraintPaths;

  /**
   * Hash Map of the current node attributes, indexed by the name of the attribute
   */
  private LinkedHashMap<String, EntityAttribute<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge>> _curNodeAtts;

  /** The edges involved in the current path being built from the XML file */
  private LinkedList<SketchEdge> _curPath;

  /**
   * The id of the current path in the XML file. This might not be the same as the
   * automatically-generated id of a new path (Easik code changes, or edge name
   * changes since the path was created). We don't actually need this for newer
   * Easik versions, since pathrefs aren't used anymore, but we need to keep it
   * for compatibility with sketches generated by older versions.
   */
  private String _curPathId;

  /** The flag indicating if the current node has been synced with a db */
  private boolean _curSketchSync;

  /** The data type of the current attribute */
  @SuppressWarnings("unused")
  private EasikType _curType;

  /** The EntityAttributes involved in the current Unique key being defined */
  private LinkedList<UniqueIndexable> _curUniqueKeyElems;

  /** The name of the current unique key */
  private String _curUniqueKeyName;

  /** The name of the current entity or constraint */
  private String _currNode;

  /** The document information for the sketch */
  private DocumentInfo _docInfo;

  /** The edges of the sketch, indexed by name */
  private LinkedHashMap<String, SketchEdge> _edges;

  /** The entity nodes of the sketch, indexed by name */
  private LinkedHashMap<String, EntityNode> _entityNodes;

  private EntityNode _curDomain; // added by ryan

  /** The current entity node */
  private EntityNode _newNode;

  /** The frame the new sketch will be placed in */
  private SketchFrame _theFrame;

  /**
   * Default Constructor
   *
   * @param inFrame
   */
  public SketchHandler(SketchFrame inFrame) {
    _entityNodes = new LinkedHashMap<>();
    _edges = new LinkedHashMap<>();
    _constraints = new LinkedList<>();
    _allPaths = new LinkedHashMap<>();
    _curConstraintPaths = new ArrayList<>();
    _allConstraintsVisible = true;
    _docInfo = new DocumentInfo(inFrame);
    _connParams = new HashMap<>();
    _theFrame = inFrame;
  }

  /**
   *
   *
   * @return
   */
  public SketchFrame getFrame() {
    return _theFrame;
  }

  /**
   * Returns boolean indicating if the current sketch has been synchronized with a
   * db.
   *
   * @return
   */
  public boolean getSyncLock() {
    return _curSketchSync;
  }

  /**
   * Returns LinkedHashMap of edges
   * 
   * @return LinkedHashMap of edges
   */
  public LinkedHashMap<String, SketchEdge> getEdges() {
    return _edges;
  }

  /**
   * Returns LinkedHashMap of entities
   * 
   * @return LinkedHashMap of entities
   */
  public LinkedHashMap<String, EntityNode> getEntities() {
    return _entityNodes;
  }

  /**
   * Returns LinkedList of constraints
   * 
   * @return LinkedList of constraints
   */
  public LinkedList<ModelConstraint<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge>> getConstraints() {
    return _constraints;
  }

  /**
   * Get the document information of the current sketch
   * 
   * @return The DocumentInfo object associated with this sketch
   */
  public DocumentInfo getDocumentInfo() {
    return _docInfo;
  }

  /**
   * Gets the connection parameters stored with this sketch
   * 
   * @return the Map of connection parameters
   */
  public Map<String, String> getConnParams() {
    return _connParams;
  }

  /**
   * Converts an Attributes XML object into a Map of String,String pairs.
   * Duplicate attributes (which Easik won't generate anyway) won't work.
   * 
   * @param atts the Attributes object to convert to a Map
   * @param omit any number of local names that should be omitted from the
   *             generated Map
   * @return a Map of String,String pairs with local attribute names as the keys,
   *         values as the values, not including any keys with a local name in
   *         <code>omit</code>.
   */
  private static Map<String, String> attributeMap(Attributes atts, String... omit) {
    LinkedHashMap<String, String> attMap = new LinkedHashMap<>();
    HashSet<String> skip = new HashSet<>(Arrays.asList(omit));

    for (int i = 0; i < atts.getLength(); i++) {
      String local = atts.getLocalName(i);

      if (local.equals("")) {
        local = atts.getQName(i);
      }

      if (!skip.contains(local)) {
        attMap.put(local, atts.getValue(i));
      }
    }

    return attMap;
  }

  /**
   * Overloaded method that is called any time the start of an element is found
   * 
   * @param namespace
   * @see org.xml.sax.helpers.DefaultHandler
   * @param localName
   * @see org.xml.sax.helpers.DefaultHandler
   * @param qName
   * @see org.xml.sax.helpers.DefaultHandler
   * @param atts
   * @see org.xml.sax.helpers.DefaultHandler
   */

  @Override
  public void startElement(String namespace, String localName, String qName, Attributes atts) {
    _currNode = qName;

    if (qName.equals("entity")) {
      String name = atts.getValue("name");
      int x = Integer.parseInt(atts.getValue("x"));
      int y = Integer.parseInt(atts.getValue("y"));

      if (_entityNodes.containsKey(name)) {
        System.err.println("Duplicate nodes found in XML");

        return;
      }
      _newNode = new EntityNode(name, x, y, _theFrame.getMModel());

      _entityNodes.put(name, _newNode);

      _curNodeAtts = new LinkedHashMap<>();
    } else if (qName.equals("attribute")) {
      EasikType type;

      // attributeType was created by old Easik versions, and is the SQL
      // type signature
      // (such as "VARCHAR(255)"). Easik now uses attributeTypeClass,
      // containing the
      // class name, and any number of extra attributes which
      // EasikType.newType() uses to
      // recreate the appropriate EasikType object.
      String typesig = atts.getValue("attributeType");

      if (typesig != null) {
        type = EasikType.typeFromSignature(typesig);
      } else {
        String typename = atts.getValue("attributeTypeClass");

        try {
          type = EasikType.newType(typename,
              attributeMap(atts, "attributeType", "attributeTypeClass", "name"));
        } catch (ClassNotFoundException e) {
          System.err.println("Invalid type found in XML: '" + typename + "' (" + e.getMessage() + ")");

          return;
        }
      }

      EntityAttribute<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge> myAtt = new EntityAttribute<>(
          atts.getValue("name"), type, _newNode);

      _curNodeAtts.put(atts.getValue("name"), myAtt);
      _newNode.addEntityAttribute(myAtt);
    } else if (qName.equals("uniqueKey")) {
      // New EASIK has noderef, telling us what we refer to. In old easik,
      // uniqueKey is under
      // the node itself (but as a result, cannot contain edge
      // references).
      String noderef = atts.getValue("noderef");

      if (noderef != null) {
        // Restore _newNode and _curNodeAtts, since we're going to need
        // them:
        _newNode = _entityNodes.get(noderef);
        _curNodeAtts = new LinkedHashMap<>();

        for (EntityAttribute<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge> att : _newNode
            .getEntityAttributes()) {
          _curNodeAtts.put(att.getName(), att);
        }
      }

      _curUniqueKeyName = atts.getValue("name");
      _curUniqueKeyElems = new LinkedList<>();
    } else if (qName.equals("attref")) {
      _curUniqueKeyElems.add(_curNodeAtts.get(atts.getValue("name")));
    } else if (qName.equals("edgekeyref")) {
      SketchEdge e = _edges.get(atts.getValue("id"));

      if (e instanceof UniqueIndexable) {
        _curUniqueKeyElems.add((UniqueIndexable) e);
      } else {
        System.err.println("Encountered an non-unique-indexable <edgekeyref> " + e);
      }
    } else if (qName.equals("edge")) {
      SketchEdge newEdge;
      String edgeType = atts.getValue("type");

      // injective is an old EASIK attribute:
      String injective = atts.getValue("injective");

      if (injective != null) {
        edgeType = atts.getValue("injective").equals("true") ? "injective" : "normal";
      }

      EntityNode source = _entityNodes.get(atts.getValue("source"));
      EntityNode target = _entityNodes.get(atts.getValue("target"));
      String id = atts.getValue("id");
      String cascadeAtt = atts.getValue("cascade");

      if (cascadeAtt == null) {
        // This is from an export before Easik had per-edge cascading
        // (in other words, before r583)
        // We use the global preferences for cascading
        String key = "sql_cascade", def = "restrict";

        if (edgeType.equals("partial")) {
          key = "sql_cascade_partial";
          def = "set_null";
        }

        cascadeAtt = Easik.getInstance().getSettings().getProperty(key, def);
      }

      SketchEdge.Cascade cascade = cascadeAtt.equals("set_null") ? SketchEdge.Cascade.SET_NULL
          : cascadeAtt.equals("cascade") ? SketchEdge.Cascade.CASCADE : SketchEdge.Cascade.RESTRICT;

      if (edgeType.equals("injective")) {
        newEdge = new InjectiveEdge(source, target, id, cascade);
      } else if (edgeType.equals("partial")) {
        newEdge = new PartialEdge(source, target, id, cascade);
      } else {
        newEdge = new NormalEdge(source, target, id, cascade);
      }

      _edges.put(id, newEdge);
    } else if (qName.equals("path")) {
      _curPath = new LinkedList<>();
      _curPathId = atts.getValue("id");
      _curDomain = _entityNodes.get(atts.getValue("domain"));
    } else if (qName.equals("edgeref")) {
      _curPath.add(_edges.get(atts.getValue("id")));
    } else if (qName.equals("sumconstraint") || qName.equals("pullbackconstraint")
        || qName.equals("productconstraint") || qName.equals("commutativediagram")
        || qName.equals("equalizerconstraint") || qName.equals("limitconstraint")) // TRIANGLES
                                              // CF2012
    {
      _curConstraintX = Integer.parseInt(atts.getValue("x"));
      _curConstraintY = Integer.parseInt(atts.getValue("y"));
      _curConstraintVisible = atts.getValue("isVisible").equals("true");
      _curConstraintPaths = new ArrayList<>();
      _allConstraintsVisible = atts.getValue("isVisible").equals("true");
    } else if (qName.equals("pathref")) {
      // This is for compatibility with old versions of Easik (pre-2.0);
      // new versions
      // put <path> elements directly inside the various constraint
      // elements.
      _curConstraintPaths.add(_allPaths.get(atts.getValue("id")));
    } else if (qName.equals("connectionParam")) {
      _connParams.put(atts.getValue("name"), atts.getValue("value"));
    } else if (qName.equals("synchronized")) {
      // The existance of this tag tells us the sketch is synchronized
      _curSketchSync = true;
    }
  }

  /**
   * Overloaded method that is called any time the end of an element is found
   * 
   * @param uri
   * @see org.xml.sax.helpers.DefaultHandler
   * @param localName
   * @see org.xml.sax.helpers.DefaultHandler
   * @param qName
   * @see org.xml.sax.helpers.DefaultHandler
   */
  @Override
  public void endElement(String uri, String localName, String qName) {
    _currNode = null;

    if (qName.equals("uniqueKey")) {
      UniqueKey<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge> newKey = new UniqueKey<>(_newNode,
          _curUniqueKeyElems, _curUniqueKeyName);

      _newNode.addUniqueKey(newKey);
    } else if (qName.equals("sumconstraint")) {
      if (_theFrame.getMModel().isSumConstraint(_curConstraintPaths)) {
        _constraints.add(new SumConstraint<>(_curConstraintPaths, _curConstraintX, _curConstraintY,
            _curConstraintVisible, _theFrame.getMModel()));
      } else {
        JOptionPane.showMessageDialog(_theFrame,
            "An error occured while loading a sum constraint.\n"
                + "Error on sum constraint between tables\n" + "path1: " + _curConstraintPaths.get(0)
                + ", path2: " + _curConstraintPaths.get(1) + "\n"
                + ModelConstraint.getTablesInvolvedForError(_curConstraintPaths),
            "Error", JOptionPane.ERROR_MESSAGE);
      }
    } else if (qName.equals("pullbackconstraint")) {
      _curConstraintPaths = (ArrayList<ModelPath<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge>>) _theFrame
          .getMModel().asPullbackConstraint(_curConstraintPaths);

      if (_curConstraintPaths != null) {
        try {
          _constraints.add(new PullbackConstraint<>(_curConstraintPaths, _curConstraintX, _curConstraintY,
              _curConstraintVisible, _theFrame.getMModel()));
        } catch (ConstraintException ce) {
        }
      } else {
        String tables = ModelConstraint.getTablesInvolvedForError(_curConstraintPaths);
        if (tables == null) {
          JOptionPane.showMessageDialog(_theFrame,
              "An error occured while loading a constraint.\n "
                  + "Error on pullback. Paths must be fully defined.",
              "Error", JOptionPane.ERROR_MESSAGE);
        } else {
          JOptionPane.showMessageDialog(
              _theFrame, "An error occured while loading a constraint.\n "
                  + "Error on pullback between tables\n" + tables,
              "Error", JOptionPane.ERROR_MESSAGE);
        }
      }
    } else if (qName.equals("equalizerconstraint")) {
      if (_theFrame.getMModel().isEqualizerConstraint(_curConstraintPaths)) {
        try {
          _constraints.add(new EqualizerConstraint<>(_curConstraintPaths, _curConstraintX, _curConstraintY,
              _curConstraintVisible, _theFrame.getMModel()));
        } catch (ConstraintException ce) {
        }
      } else {
        JOptionPane.showMessageDialog(_theFrame,
            "An error occured while loading a constraint.\n"
                + "Error on equalizer constraint between tables\n"
                + ModelConstraint.getTablesInvolvedForError(_curConstraintPaths),
            "Error", JOptionPane.ERROR_MESSAGE);
      }
    } else if (qName.equals("productconstraint")) {
      if (_theFrame.getMModel().isProductConstraint(_curConstraintPaths)) {
        _constraints.add(new ProductConstraint<>(_curConstraintPaths, _curConstraintX, _curConstraintY,
            _curConstraintVisible, _theFrame.getMModel()));
      } else {
        JOptionPane.showMessageDialog(_theFrame,
            "An error occured while loading a constraint.\n"
                + "Error on product constraint between tables\n"
                + ModelConstraint.getTablesInvolvedForError(_curConstraintPaths),
            "Error", JOptionPane.ERROR_MESSAGE);
      }
    } else if (qName.equals("commutativediagram")) {
      if ((_curConstraintPaths.size() >= 2) && _theFrame.getMModel().isCommutativeDiagram(_curConstraintPaths)) {
        _constraints.add(new CommutativeDiagram<>(_curConstraintPaths, _curConstraintX, _curConstraintY,
            _curConstraintVisible, _theFrame.getMModel()));
      } else {
        JOptionPane.showMessageDialog(_theFrame,
            "An error occured while loading a constraint.\n"
                + "Error on commutative diagram between tables\n"
                + ModelConstraint.getTablesInvolvedForError(_curConstraintPaths),
            "Error", JOptionPane.ERROR_MESSAGE);
      }
    } else if (qName.equals("limitconstraint")) { // TRIANGLES CF2012
      if (_curConstraintPaths != null) {
        _constraints.add(new LimitConstraint<>("LC", _curConstraintX, _curConstraintY, _curConstraintVisible,
            _theFrame.getMModel(), _curConstraintPaths));
      } else {
        JOptionPane.showMessageDialog(_theFrame,
            "An error occured while loading a constraint.\n " + "Error on pullback between tables\n"
                + ModelConstraint.getTablesInvolvedForError(_curConstraintPaths),
            "Error", JOptionPane.ERROR_MESSAGE);
      }
    } else if (qName.equals("path")) {
      ModelPath<SketchFrame, SketchGraphModel, Sketch, EntityNode, SketchEdge> myPath;
      if (_curPath.isEmpty()) {
        myPath = new ModelPath<>(_curDomain);
      } else {
        myPath = new ModelPath<>(_curPath);
      }

      _allPaths.put(_curPathId, myPath); // For old Easik sketch
                        // compatibility
      _curConstraintPaths.add(myPath);
    } else if (qName.equals("constraints")) {
      _theFrame.setShowConstraints(_allConstraintsVisible);
    }
  }

  /**
   * @see org.xml.sax.helpers.DefaultHandler
   * @param ch
   * @see org.xml.sax.helpers.DefaultHandler
   * @param start
   * @see org.xml.sax.helpers.DefaultHandler
   * @param length
   * @see org.xml.sax.helpers.DefaultHandler
   */
  @Override
  public void characters(char[] ch, int start, int length) {
    if (_currNode == null) {
      return;
    }

    String value = new String(ch, start, length);

    if (_currNode.equals("title")) {
      _docInfo.setName(value);
    } else if (_currNode.equals("author")) {
      _docInfo.addAuthor(value);
    } else if (_currNode.equals("description")) {
      _docInfo.setDesc(value);
    } else if (_currNode.equals("creationDate") || _currNode.equals("lastModificationDate")) {
      Date date;

      try {
        date = EasikConstants.XML_DATETIME.parse(value);
      } catch (java.text.ParseException pe) {
        date = null;
      }

      if (_currNode.equals("creationDate")) {
        _docInfo.setCreationDate(date);
      } else {
        _docInfo.setModificationDate(date);
      }
    }
  }
}
