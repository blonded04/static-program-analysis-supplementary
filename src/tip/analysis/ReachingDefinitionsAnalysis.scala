package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast.AstOps.AstOp
import tip.ast._
import tip.cfg._
import tip.lattices._
import tip.solvers._

abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(false) {
  val lattice: MapLattice[CfgNode, PowersetLattice[AStmt]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunEntryNode => lattice.sublattice.bottom
      case r: CfgStmtNode =>
        r.data match {
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier =>
                s.filterNot(
                  stmt =>
                    stmt.appearingIds
                      .filter(s => s.isInstanceOf[AIdentifierDeclaration])
                      .map(s => s.asInstanceOf[AIdentifierDeclaration].name)
                      .contains(id.name)
                ) + as
              case _ => ???
            }
          case varr: AVarStmt =>
            val stmts = varr.declIds.map(id => AVarStmt(List.apply(id), varr.loc)).toSet[AStmt];
            lattice.sublattice.lub(s, stmts)
          case _ => s
        }
      case _ => s
    }
}

class ReachingDefinitionsAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

class ReachingDefinitionsAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies
