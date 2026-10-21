## Worker report

The module `Sheaf.AlgebraicGeometry.CoconeDerivedComparisonNormalForm` states
`AlgebraicGeometry.ProEtale.derivedExtendScalarsCompIso_normalForm`. Its only proof is
`sorry`. The helper definition `CategoryTheory.Mod.unitNormalizedDerivedScalarCompIso`
constructs the right-hand expression with real data, directly from the existing
adjunction and derivation APIs. It introduces no new mathematical notion, instance, or
postponed theorem. Only the
item's `lean` field changes. No statement correction or dependency repair is needed.

The source is the full paragraph of main-20261015, sec-six-functors-basics/
sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md and the fixed
`derivedExtendScalarsCompIso` construction in TwoColimit.lean. The current server source
was checked with `scompile.py --source`; it currently spells the construction directly,
just as the read clone does. Its two factors are inverse exact-derived composition and
left derivation of the underived composition/equal-map comparison.

Hypotheses and clauses, in order:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. An arbitrary scheme is `(X : Scheme.{u})`,
  with the universe `u` explicitly declared. There is no noetherian, boundedness,
  nonemptiness, or constructibility hypothesis.
- The finite intermediate extensions inside the fixed algebraic closure are
  `{E H : PadicAlgCl.FiniteIntermediateField ℓ}`, with `(h : E ≤ H)` the inclusion.
  This reuses the project's finite-dimensional intermediate-field subtype.
- The coefficient ring objects are the endpoints of `padicSubfieldRingObjMap X ℓ h`
  and `padicSubfieldRingObjToPadicAlgCl X ℓ H`. The latter lands in the existing
  `padicAlgClRingObj X ℓ`, namely `condensedRingObj (Profinite.padicAlgClRingObj ℓ) X`.
  Its condensed sections are continuous maps valued in one finite subextension;
  this is not a replacement by all algebraic-closure-valued continuous functions.
- The maps phi, psi, kappa are respectively `padicSubfieldRingObjMap X ℓ h`,
  `padicSubfieldRingObjToPadicAlgCl X ℓ H`, and
  `padicSubfieldRingObjToPadicAlgCl X ℓ E`. The equality psi phi = kappa is precisely
  `padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h`.
- The functors A and B are `Mod.extendScalars` of the first two maps. Their composite
  BA is `Mod.extendScalars phi ⋙ Mod.extendScalars psi` in Lean's diagrammatic order.
  D is extension along `phi ≫ psi`, and C is extension along kappa. These are internal
  module objects in `Sheaf (ProEt.topology X) Ab.{u + 1}`, not ordinary modules over
  an underlying ring.
- The unit-compatible comparison u is written out using `Adjunction.leftAdjointUniq`,
  applied first to the composite extension/restriction adjunction and second to
  `Mod.extendRestrictAdjunction (phi ≫ psi)`. For the first adjunction,
  `.ofNatIsoRight (Mod.comapComp phi psi).symm` identifies the composite restriction
  with restriction along the composite. Thus both right adjoints are the very same
  `Mod.comap (phi ≫ psi)`. Mathlib's `unit_leftAdjointUniq_hom_app` gives exactly
  `eta_BA ≫ R.map u = eta_D`; this is the recorded dependency's common-right-adjoint
  special case, with the correct direction BA to D. No arbitrary isomorphism or
  extra normalization hypothesis is supplied.
- The specified e is `Mod.extendScalarsIsoOfEq` of the recorded coefficient-map
  equality. The expression `u ≪≫ e` in the helper body therefore means e after u, with
  endpoints BA, C.
- L is the existing total `leftDerivedFunctor`. The c in the node is
  `Functor.leftDerivedFunctorCompIso A B`, whose source is `L(A ⋙ B)` and whose
  target is `LA ⋙ LB`. This is the canonical transport of
  `mapDerivedCategoryCompIso` through the exact-functor identifications. The imported
  `existsUnique_mapDerivedCategoryCompIso` identifies that comparison by the node's
  specified localization equation, after the same transport. The first factor on
  the right is `.symm`, hence c inverse.
- In the helper body, `Functor.leftDerivedFunctorNatIso (A ⋙ B) (u ≪≫ e)` is
  L(e after u). Its definition
  uses `mapDerivedCategoryNatIso`, which is exactly the dependency's
  `Localization.liftNatIso` applied to the termwise isomorphism, transported through
  the fixed exact-derived identifications. No second derived operation is defined.
- The left side is `derivedExtendScalarsCompIso X ℓ h`, not a quantified comparison.
  The right side specializes the helper at phi, psi, kappa and their recorded equality;
  its body is exactly c inverse followed by L(e after u). Equality is equality of
  natural isomorphisms between these fixed functors, so both their transformations
  and inverse transformations agree, on all objects and arrows. The LA, LB, LC
  endpoints are definitionally the recorded `derivedExtendScalarsSubfield` and
  `derivedExtendScalarsToPadicAlgCl`; no replacement functor or automorphism enters.

Dependency declarations read and reused:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `AlgebraicGeometry.ProEtale.derivedExtendScalarsSubfield`,
  `derivedExtendScalarsToPadicAlgCl`, and `derivedExtendScalarsCompIso`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicSubfieldRingObj`, `padicAlgClRingObj`, `padicSubfieldRingObjMap`,
  `padicSubfieldRingObjToPadicAlgCl`, `padicSubfieldRingObjMap_comp_toPadicAlgCl`,
  and the finite-limit preservation instances for both scalar extensions. This module
  is publicly imported by TwoColimit; it supplies both flatness proof dependencies.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `CategoryTheory.Mod.extendScalars`, `extendRestrictAdjunction`, `extendScalarsComp`;
  restriction and its composition are the existing `Mod.comap` and `Mod.comapComp`.
  This module is publicly imported by ChangeOfScalarsSquare.
- `Mathlib.CategoryTheory.Adjunction.Unique`:
  `CategoryTheory.Adjunction.leftAdjointUniq` and
  `unit_leftAdjointUniq_hom_app`, the explicitly recorded common-right-adjoint
  specialization of lem-weil-pbc-conjugate-iso-unit-equation. Its general mate interface
  in Adjunction.Mates was also read.
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`:
  `CategoryTheory.Mod.extendScalarsIsoOfEq`.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`:
  `CategoryTheory.Functor.leftDerivedFunctor`,
  `leftDerivedFunctorIsoMapDerivedCategory`, `leftDerivedFunctorCompIso`, and
  `leftDerivedFunctorNatIso`. These are the left-derived and exact-functor components
  of the convention node sk-def-sfb-derived-categories. That node's primary
  rightDerivedFunctorOfQuasiIsoResolutions interface was read but is not used here;
  importing it would introduce an irrelevant right-derived construction.
- `Sheaf.CategoryTheory.ExactDerivedComposition`:
  `CategoryTheory.Functor.existsUnique_mapDerivedCategoryCompIso`, a nonpublic
  proof-plan import for the unique normalized composition comparison.
- `Mathlib.CategoryTheory.Localization.Predicate`:
  `CategoryTheory.Localization.liftNatIso`, `liftNatTrans_app`, and `natTrans_ext`.
  These are the recorded natural-isomorphism dependency and localization universal
  property used in proof steps 3-4. ExactFunctor's `mapDerivedCategoryNatIso` is the
  existing specialization used by `leftDerivedFunctorNatIso`.

Edge cases checked before writing: E = H and reflexive h remain valid (no strict
inclusion is assumed); the zero complex and arbitrary unbounded complexes are included;
the empty scheme is included; every prime is covered; no finite-dimensionality or
finiteness is imposed on a complex. The pro-etale site and Ab universes are inherited
from the actual coefficient functors, with no added equality between object and
morphism universes. D need not be derived separately in the signature: it is the middle
endpoint of u and e before applying L to their composite.

Searches for an existing statement (2026-10-21):

- msearch.py leanfinder, query: "The specified derived scalar extension cocone comparison
  equals the inverse exact derived composition comparison followed by the derived unit
  compatible underived scalar extension comparison". Eight hits, including
  `CategoryTheory.Abelian.Ext.mapExactFunctor_hom` and generic
  `LocalizerMorphism.rightDerivedFunctorComparison` results; none is this normalization.
- msearch.py loogle, query: `CategoryTheory.Adjunction.leftAdjointUniq`. Twelve hits,
  including `leftAdjointUniq`, its unit equations, inverse formula and transitivity.
  These supply u and its normalization, not the claimed derived cocone equation.
- msearch.py grep, query:
  `leftDerivedFunctorCompIso|leftDerivedFunctorNatIso|derivedExtendScalarsCompIso`,
  in Mathlib/CategoryTheory: zero hits. These exact-derived constructions are upstream
  project declarations, not a Mathlib theorem about this cocone.
- msearch.py leansearch, query: "Canonical composition comparison for total derived
  scalar extension agrees with the derived unit compatible adjunction isomorphism".
  Eight hits, including `ModuleCat.extendScalarsComp` and generic derived adjunction
  units; no exact match for internal modules and this specified cocone comparison.
- rg in WeilConjectures and Sheaf for the node id and for derivedExtendScalarsCompIso,
  finiteCoefficientDerivedTensorCompIso, normalForm, cocone/comparison and
  leftAdjointUniq/extendRestrict: found the actual fixed construction and its cached
  older presentation, and coefficient-complex component transport theorems. None
  states this global isomorphism equality with the reversed unit-compatible adjunction
  comparison. In particular CondensedCoefficientComplexDerivedTransport identifies
  components on localized coefficient complexes, not this normal form. The new
  declaration name has no existing match. No notion is duplicated.

No STATEMENT-DISPUTED finding or node fault.

## Second reading by Q46

A separate pass re-read the node, the full Lean signature, and the definitions of
extendScalarsComp, extendScalarsIsoOfEq, leftDerivedFunctorCompIso and
leftDerivedFunctorNatIso. This is a worker self-check; the dispatcher explicitly forbids
starting another agent, and the maintainer supplies the independent delivery review.

The binders match prime, arbitrary scheme, finite intermediate fields and non-strict
inclusion exactly. Tracing the underived endpoints gives BA -> D -> C. In particular
leftAdjointUniq starts with the composite adjunction, not the adjunction for D, and
comapComp is reversed when transporting the right adjoint. Tracing the derived endpoints
gives LA LB -> L(BA) -> LC. Diagrammatic `≪≫` reverses the displayed functional
composition convention exactly as needed. The equation names the fixed delta and uses
fixed canonical L comparisons; it is not an existence statement, an equation merely on
cohomology, or a statement about an arbitrary isomorphism. Finite-subextension-valued
condensed coefficients, the full unbounded categories, reflexive inclusion, zero
complexes and the empty scheme are retained. The definitions of the named derived
extension functors verify the stated LA/LB/LC identifications on objects and arrows.
No mathematical mismatch was found and no mathematical statement was changed.
The expanded expression initially timed out because it repeatedly synthesized the
graded tensor structures after specializing to coefficient sheaves. The final helper
shares those structures in the generic module category, with composition exactness
supplied by the existing comp_preservesFiniteLimits/Colimits theorems. Specializing
it imposes no additional hypotheses on the theorem, and its body exposes both canonical
factors in full. The sandbox and final library-module compilation use the same file;
no local notation, private declarations, file-local instance declarations, or option changes
are left in the final source.

Validation: scompile.py compiled both the sandbox and the final library module cleanly
(23.7 s and 19.7 s respectively), within the unchanged 60-second per-file limit.
