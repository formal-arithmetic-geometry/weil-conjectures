## Worker report

This is a stage-2 statement delivery on the accepted Q43 five-step split. The prior
supersession was a stage-1 failure; coord/brief-stage2.md section 0 explicitly distinguishes
that from this assignment. The Q47 return dated 2026-10-23 12:20 UTC also requests this
precise stage-2 delivery. No split, statement, source, dependency, or review field is changed.
The retained sandbox contained only dispatcher brief markers and no prior Lean work.

The module Sheaf.CategoryTheory.InternalBarFiniteIndexTransfer states
CategoryTheory.CondensedBar.internal_bar_finite_index_transfer with one sorry theorem.
All helper data are actual constructions on the recorded bar models. No new notion,
dependency module, or statement correction is introduced.

Hypothesis and clause correspondence:

- A commutative condensed ring: `A : Ring.{u}`, the existing CommMon of abelian sheaves
  on `coherentTopology Profinite.{u}`. The zero ring is not excluded. Its underlying ring
  and modules are the existing Profinite.CondensedRing and CategoryTheory.Mod encodings.
- Profinite G: `G : Type u` with Group, TopologicalSpace, IsTopologicalGroup,
  CompactSpace, T2Space and TotallyDisconnectedSpace. The single explicit universe u
  implements the recorded small-site convention, with coefficient sections in u+1.
- Every open subgroup, including G: `H : OpenSubgroup G`. Its actual subgroup type is
  `H.toSubgroup`; this avoids a typeclass failure of the OpenSubgroup carrier spelling.
  Compactness comes from the existing closedness theorem, not a new hypothesis.
- Arbitrary nonnegative equivariant I: the conclusion quantifies over every
  `I : CochainComplex (Equivariant A G) ℕ`; no injectivity or resolution condition.
- D_J is internal Hom of the free parameter module: F is the recorded InternalFunctions
  presentation, including its `internalHom : functor P ≅ Mod.ihom (freeParameter A P)`;
  B and BH are its recorded BarDiagram presentations with the exact action-dependent
  cofaces. These are coordinate presentations of the specified bar construction, not
  arbitrary replacements or extra exactness assumptions. They retain arbitrary A.
  `barTransferDouble (cochains B)` is definitionally the recorded `doubleComplex B`;
  the subgroup version applies the same construction after the existing action inflation
  along the actual continuous subgroup inclusion, hence uses exactly the same I.
- Restriction r_H: existential r is fixed on every generalized evaluation by the first
  conjunct: `B.term.inv ≫ r.f p.f q ≫ BH.term.hom` evaluates by composing the parameter
  map with `barTransferPowerInclusion H p`. The formula includes all S,T,f,g,x and
  p=q=0, so is precisely restriction on internal Hom, before evaluating cohomology.
- Internal linear transfer t_H^{p,q}: `((t.app I).f p).f q`; r and t are natural
  transformations into the category of double complexes. They are internal A-module
  morphisms, not maps of point sections. Their bicomplex morphism laws express both
  d_h t=t d_h and d_v t=t d_v.
- h_H^{p,q}: `((h I).hom p (p-1)).f q`, with the degree-zero map zero by
  `Homotopy.zero`: the shape condition would require (p-1)+1=0 in degree zero.
  More generally `h.hom i j` is zero unless j+1=i. The homotopy components are vertical
  cochain maps, so their commutation condition is d_v h=h d_v with no sign.
- t r - index = d_h h + h d_h: `Homotopy (r.app I ≫ t.app I)
  (H.toSubgroup.index • 𝟙 ...)` has exactly this content by Homotopy.comm;
  categorical composition r then t is mathematical t composed with r.
- Naturality with a single choice for all I: r,t are natural transformations and h
  is chosen simultaneously for all I, with its explicit second-conjunct naturality
  equality for every equivariant chain map I→J. No normality assumption on H is made.
- Compatibility with all profinite test restrictions: every component is a morphism
  in the recorded internal module category, whose underlying `.hom.hom` is a natural
  transformation of sheaves. Its naturality at k.op gives restriction compatibility
  for every k:T→S. The first conjunct additionally quantifies over every base change
  in the function-evaluation presentation. No pointwise evaluation/cohomology exchange.
- Internal V_{J,q}: `barTransferVerticalCohomology A q` applies the actual
  HomologicalComplex.homologyFunctor to the vertical columns and their differentials.
  This uses internal kernels and sheaf images in Modules A; it does not compute the
  cohomology of an evaluated section complex.
- Induced cochain maps and homotopy: the third conjunct supplies hv between the images
  of the SAME r,t, whose components equal `homologyMap ((h I).hom i j) q`.
- E_J^{p,q} and final index identity: the fourth conjunct applies homologyMap in degree
  p to these induced cochain maps; their composite is
  `H.toSubgroup.index • 𝟙` on the group-side internal iterated homology object.
- No vanishing, rationality, norm, completeness or coefficient topology assumption
  appears. Index multiplication is natural-number repeated addition, not division.

Dependency declarations read and used:

- sk-def-sfb-condensed-ring: Sheaf.Topology.ProfiniteCondensedRing,
  Profinite.CondensedRing, through CondensedBar.Ring and Modules.
- def-weil-size-convention: metatheoretic convention, explicit universe u and the
  recorded coherent profinite site; its record correctly has no declaration.
- sk-def-sfb-module-objects: Mathlib.CategoryTheory.Monoidal.Mod, CategoryTheory.Mod,
  including ModObj and its linear morphisms, through CondensedBar.Modules.
- def-sfb-condensed-action-module: Sheaf.CategoryTheory.CondensedActionModule,
  Profinite.CondensedAction.ActionModule and inflate, through CondensedBar.Equivariant.
- def-sfb-condensed-equivariant-bar-data:
  Sheaf.CategoryTheory.CondensedEquivariantBarData, Ring, Modules, sections,
  InternalFunctions, BarDiagram, power, cochains and doubleComplex.
- def-sp-double-complex-total: WeilConjectures.CategoryTheory.DoubleComplexTotal,
  and its Mathlib HomologicalComplex₂, flipFunctor, homologyMap and homologyFunctor
  interfaces. Its module is also imported for the proof plan.
- sk-def-sfb-derived-categories: read the recorded right-derived interface and its
  docstring in RightDerivedFunctorOfQuasiIsoResolutions. This statement needs only
  nonnegative cochain complexes and internal homology, supplied by the above imports;
  it does not introduce a second localization or derive an unrelated functor.

The accepted proof steps are reproduced in the theorem docstring. The homogeneous
coordinate, vertex-prism and finite-coset proof dependencies currently have no Lean
records and cannot be imported; no replacement statements are invented. The recorded
bar-data and double-complex proof dependencies are imported. Their absence does not
prevent stating this item with sorry, as required by this assignment.

Edge cases checked before writing and during the clause audit:

- H=G: singleton transversal, identity transfer and zero homotopy are possible;
  index is 1. No proper-subgroup or nontrivial-group assumption is present.
- Trivial G: included by the same typeclass binders.
- Degree zero: power G 0 is terminal; restriction still uses the prescribed evaluation.
  Homotopy shape forces h_0=0, and its comm equation is the required degree-zero one.
- Zero complex and zero coefficient ring: all morphisms/identities are interpreted
  internally and no Nontrivial assumption is used.
- q=0 and arbitrary p,q: all conjuncts quantify over ℕ, without positivity conditions.
- Empty profinite test sets: S and T range over all Profinite, including empty ones.
- Non-normal open H and nontrivial coefficient action: inflate is along the inclusion;
  the bar faces use the restricted action, not trivial coefficients.

Searches (2026-10-23):

- msearch.py leanfinder, "Finite index transfer restriction internal condensed module
  bar cochains chain homotopy multiplication by index": 8 hits, including
  ContinuousCohomology.MultiInd.complex, homogeneousCochains and discrete Rep bar
  definitions, but no internal condensed-module transfer with vertical compatibility.
- msearch.py loogle, `"groupCohomology", "transfer"`: 0 hits.
- msearch.py grep, `transfer|corestrict`, Mathlib/Condensed: 0 hits.
- msearch.py leansearch, "Finite index subgroup restriction transfer internal sheaf bar
  double complex homotopy": 8 hits, on Subgroup.FiniteIndex, MonoidHom.transfer,
  Rep.resIndAdjunction and groupHomology.indIso; none is this internal bicomplex result.
- rg on lean/WeilConjectures and lean/Sheaf for the item id, finiteIndexTransfer,
  bar.*[Tt]ransfer and transfer.*[Bb]ar: no matching theorem (one unrelated comment
  in EmbeddingExtension). Exact search of all delivered declaration names in those
  trees and Mathlib gives no pre-existing declaration.
- Read the recorded dependency sources and Mathlib Homotopy, HomologicalBicomplex,
  Additive, ShortComplex/HomologicalComplex and OpenSubgroup interfaces, including
  full types and explanatory docstrings used above. No duplicate notion is introduced.

Validation: scompile.py compiles both the sandbox probe and the library module cleanly
(2026-10-23, sandbox 15.1 s, library 3.1 s). No diagnostic commands remain. All binders
are explicit (`set_option autoImplicit false`). All lines are at most 100 characters.
There is no STATEMENT-DISPUTED issue or source correction.

## Second reading by Q77

No independent worker reading is claimed: the dispatcher expressly prohibits starting
other agents. As specified by the current direct-delivery workflow, the maintainer's
independent review reads this delivery. I re-read the node and final Lean signature
clause by clause in this session, checking the categorical composition order,
vertical versus horizontal indices, the subgroup action, degree-zero shape and
that the final equality uses the maps induced by the very same r,t,h. This found no
remaining mismatch. The compiler repair used the subgroup's actual toSubgroup type
and an explicit additive-hom map identity, without adding hypotheses or changing
any mathematical clause.
