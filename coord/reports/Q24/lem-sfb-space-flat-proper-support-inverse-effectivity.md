## Worker report

The module Sheaf.AlgebraicGeometry.SpaceFlatProperSupportInverseEffectivity states
Stacks Project, spaces-flat.tex, Situation 0CX4 and Theorem 0CXB. The source was
read in literature/stacks-project/spaces-flat.tex, lines 2144--2167 and 2384--2428.
The node statement, statement dependencies, and five-step proof are unchanged.
The theorem and the two canonical-map commuting-triangle obligations have sorry
proofs; the base, tests and test maps have explicit data. These helpers belong to
the effectivity statement itself, rather than defining an independent notion.
All six declarations are listed in lean.declarations and carry source/blueprint
docstrings. No definition chooses an arbitrary map, functor or algebraization.

Hypotheses and clauses, in node order:

- The inverse sequence is D : ℕᵒᵖ ⥤ CommRingCat.{u}. Index n in Lean is n+1
  in the node, so index 0 is exactly the first ring, not an additional ring.
  Adjacent transitions are D.map (homOfLE (Nat.le_succ n)).op. Giving the functor
  records every composite transition and its functor laws, with no extra data.
- hsurj is surjectivity of each adjacent ring map. hnil quantifies over each
  individual element x of its kernel and asserts IsNilpotent x. It imposes no
  uniform nilpotence exponent and no Noetherian or adic-completeness condition.
- A is the actual categorical limit D in commutative rings. inverseEffectivityBase
  is Spec (limit D), embedded by the existing schemeSpace, not an arbitrary model.
  Explicit universe u is shared by these rings and schemes; the existing space
  site has objects in u+1 and module section carriers in u. No equality between
  different site universes, smallness restriction on a chart, or extra size
  hypothesis is added.
- X is an algebraic space over Spec (limit D). The map a targets the actual
  representable base. hsep is MapIsSeparated a and hfp is the existing
  ProperQuotFinitePresentation a: local finite presentation, quasi-compactness,
  and quasi-compact diagonal. Neither flatness nor properness of a is required.
- inverseEffectivityTest D n is the actual Spec of the limit projection to A_n,
  regarded as a scheme over Spec A with its Yoneda map. Consequently
  properQuotFibre a (inverseEffectivityTest D n) is precisely X_n = X ×_A Spec A_n.
  properQuotFst and properQuotSnd are its two existing projections.
- Mn is a module on the small etale ringed site of each actual X_n. hqc uses
  SheafOfModules.IsQuasicoherent; hmfp uses IsFinitePresentation, which says
  etale locally a cokernel between finite rank free modules.
- hflat tests every etale scheme chart U of X_n using schemeRestriction and the
  recorded Scheme.Modules.IsFlatOver of its actual scheme map to Spec A_n.
  For the quasi-coherent Mn this is equivalent to the stated stalk condition.
- hsupp is exactly the existential criterion from def-sfb-space-proper-quot-functor:
  a representable closed immersion i:Z→X_n, MapIsProper of Z→Spec A_n, and a
  finite type quasi-coherent G with Nonempty (i_*G ≅ Mn n). These are not arbitrary
  topological support predicates, and no flatness of G or of the carrier is added.
- transition supplies the specified isomorphism from tensor pullback of Mn (n+1)
  along the canonical adjacent fibre map to Mn n. inverseEffectivityTestStep uses
  Spec of the original ring transition. Its two named commuting-triangle theorems
  only supply proof fields of this explicit construction. The pullback is the
  recorded moduleTensorPullback, with no private replacement.
- The existential conclusion supplies M : X.Modules with the same four conditions:
  quasi-coherence, finite presentation, relative chartwise flatness over Spec A,
  and the identical proper closed carrier criterion over Spec A.
- e supplies actual isomorphisms from tensor pullback of M along each
  properQuotFst to Mn n. The final equality has common source the iterated pullback
  of M to X_n: properQuotSourceIso.hom followed by e_n equals pullback of e_{n+1}
  followed by the GIVEN transition_n. properQuotSourceIso uses the existing tensor
  associator normalized on pure local tensors. This retains every prescribed
  transition, including twists by automorphisms, rather than only objectwise
  isomorphism classes. Adjacent compatibility implies compatibility with composite
  transitions because the indexing category is the free chain and tensor
  associativity is the canonical one.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom, Spec,
  and Spec.map (def-pc-scheme and def-weil-affine-spectrum).
- def-weil-size-convention is metatheoretic and has no defining declaration;
  explicit universe u and the existing module/site universe conventions render it.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.EtaleSite, structureSheaf and Modules (def-trf-algebraic-space).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace; properQuotFibre uses this very sheaf fibre product.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its slice
  sheafification instances, using Mathlib's IsQuasicoherent unchanged.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent: IsQuasicoherent and
  IsFinitePresentation; Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators:
  IsFiniteType (the predicates already used by the proper-support Quot interface).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleTensorPullback
  and moduleDirectImage, specified by the recorded direct-image model and adjunction.
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic:
  Scheme.Modules.IsFlatOver. Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction:
  schemeRestriction supplies the chartwise restriction used by the existing Quot
  declaration, not a second relative-flatness definition.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsSeparated and
  MapIsProper. IsRepresentableWith applied to IsClosedImmersion is the closed
  immersion convention used by the recorded proper-support Quot declaration.
- Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor: ProperQuotFinitePresentation,
  ProperQuotTest, properQuotFibre, properQuotFst, properQuotSnd,
  properQuotFibreMap and properQuotSourceIso. Their public dependencies expose
  the preceding foundational declarations. The source iso in turn uses
  moduleTensorComposition from SpaceFlatDirectImageBaseChange, normalized on tensors.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: schemeSpace, publicly exposed
  through the proper-support Quot module, is the existing representable-space model.
- Proof-only import Sheaf.AlgebraicGeometry.NilpotentTowerMonomorphismRigidity:
  AlgebraicGeometry.isIso_of_nilpotentTower. The other three proof helper nodes,
  lem-sfb-space-inverse-modules-near-special-fibre,
  lem-sfb-space-inverse-module-proper-shrinking, and
  lem-sfb-space-proper-support-universal-flattening, have no recorded Lean module
  in the read checkout, so there is no module to import for them. None is needed
  to type this theorem; its docstring retains their complete five-step assembly.

Edge cases checked before drafting: the zero/empty module system is permitted;
the zero ring gives an empty base and causes no excluded case; a constant tower
has identity ring transitions but arbitrary supplied module transition
isomorphisms, and the final equation retains these; elementwise nilpotent kernels
need not be nilpotent ideals; finitely presented nonflat X is allowed, since
flatness is imposed only on Mn and the resulting M; supports can be strictly
smaller than X_n and no annihilator-base-change assertion is introduced. There
is no finite-length tower or extra n=0 reduction. Every universe and variable
is bound explicitly, with autoImplicit false. No statement fault or disputed
mathematical assertion was found.

Searches (msearch.py, group Q24 and this item):

- leanfinder query "Grothendieck existence inverse sequence surjective locally
  nilpotent kernels algebraic space flat finitely presented modules proper
  support effectivity": eight hits on affine-transition limits and flat descent;
  no matching theorem.
- loogle query '"IsNilpotent", "Surjective"': two hits on Lie algebra/module
  nilpotence; no matching theorem.
- grep query 'Grothendieck.*[Ee]xistence|inverse.*effectiv|proper.*support.*inverse':
  no Mathlib hits.
- leansearch query "Grothendieck existence algebraic space modules inverse system
  proper support flat": eight hits on flat modules and flat scheme morphisms;
  no inverse-system algebraization theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the item id and the preceding
  existence/effectivity patterns found the classical Grothendieck-existence
  modules and the proof mention in SpaceCoherentStackGeneral. The classical
  upstream theorem was opened: it concerns schemes over a Noetherian adically
  complete ring and powers of one ideal, so it does not state this node.
- rg of both library roots and dag/lean_names_upstream.json for the six proposed
  declaration names found no pre-existing declaration. Further source searches
  located the actual Quot, module predicates, scheme restriction and tensor
  associator, which are reused unchanged.

## Second reading by Q24

A separate manual pass compared the node, source Situation 0CX4 / Theorem 0CXB,
and the finished signature. No other agent was started, as instructed by the
launcher; this paragraph records the worker's second pass, not an independent
agent review. The maintainer's independent review remains the delivery review.

The audit matched hsurj, the elementwise hnil, separatedness and the three finite
presentation clauses, all four Mn conditions, the specified adjacent transition
isomorphisms, all four conditions on M, and every required reduction isomorphism.
In particular the compatibility equation is typed on iterated pullbacks and uses
properQuotSourceIso in the correct direction: its hom first, then e_n; on the
other side pullback of e_{n+1}, then the supplied transition. The schemes have
not been substituted for algebraic spaces, and no Noetherian, ambient-flatness,
proper-ambient-space, uniform-nilpotence, or arbitrary-comparison hypothesis was
introduced. The helper data really are Spec of the limit projections/transitions.
The first compile exposed an underdetermined source of Over.homMk in the test
construction; it was fixed by explicitly naming Over.mk (Spec.map (limit.π ...)).
This is an elaboration annotation and changes no mathematical clause.
