## Worker report

Item: `lem-pur-etale-quotient-tensor-stalk-criterion`, stage 2, group N8.

The module `Sheaf.AlgebraicGeometry.EtaleQuotientTensorStalkCriterion` states
`AlgebraicGeometry.Scheme.etale_quotient_tensor_stalk_criterion` with `sorry`.
Two real-data helpers belonging to this node spell out its generator and its
normalized quotient-stalk hypothesis. There are no new independent notions or
new nodes, no dependency repair, and no change to the informal statement.

Hypothesis and clause correspondence:

- The commutative coefficient ring is `A : Type (u + 1)` with `[CommRing A]`;
  the arbitrary scheme is `T : Scheme.{u}`. There is no finiteness, nonzero-ring,
  noetherian, separatedness, or geometric hypothesis on T. As in the existing
  constant-module equivalence and support-quotient consumers, the module universe
  is one above the scheme universe; a smaller coefficient ring can be lifted.
  `T.smallEtaleTopology` is the recorded small etale site; its essentially small
  presentation is the existing framework's universe convention, with no new site.
- Ordinary modules over the constant ring sheaf are encoded by
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`. The published
  `Scheme.etaleConstantModuleFunctor` identifies this category with modules over
  the constant ring sheaf, retaining the underlying abelian sheaf and the scalar
  action. This is the same encoding used by `SupportQuotientFlat` and
  `SupportQuotientProduct`. It is not a replacement coefficient category.
- `E D : Set T` are arbitrary subsets of the scheme's topological points.
  `F G H` are the three module sheaves. Their quotient maps `q s r` have source
  `𝟙_ (Sheaf ... (ModuleCat A))`, the constant ring module. `[Epi q]`, `[Epi s]`,
  `[Epi r]` retain all three epimorphism assumptions.
- `hflat : exactFunctor _ _ (tensorRight F)` says exactly that tensoring on the
  right with F is exact. This is the existing predicate exposed by the recorded
  flatness module for the module-valued-sheaf encoding (see its lean.note), not a
  newly defined flatness condition. Flatness remains assumed even though the
  proof does not use it.
- `EtaleQuotientStalkNormalized A T S q` quantifies over every algebraically closed
  field `Ω : Type u` and point `t : Spec Ω ⟶ T`. The underlying topological point
  is `t (IsLocalRing.closedPoint Ω)`. On S it asks for an A-linear categorical
  isomorphism `i : stalk F ≅ ModuleCat.of A A` such that `stalk.map q ≫ i.hom`
  equals the canonical unit-stalk map `Functor.OplaxMonoidal.η stalk`. Under the
  canonical constant-ring stalk identification this is exactly the identity on A.
  Off S it asks `IsZero (stalk F)`: equivalently the unique identification with the
  zero A-module, where the quotient map is necessarily zero. Thus no off-support
  identification or map condition is lost. The three hypotheses `hq hs hr` apply
  this to E, D, and `E ∩ D`, respectively. The conclusion quantifies over *every*
  compatible on-support identification, so none of the specified identifications
  is silently replaced by a different one.
- The stalks are the existing `pointSmallEtale` sheaf fibers, universe-lifted as in
  `EtaleStalkTensorScalar`. Their diagram is the opposite pointed-neighborhood
  colimit of the recorded `pointedEtaleStalk`; no second stalk is constructed.
- `etaleQuotientTensorGenerator A T q s` is definitionally
  `(λ_ (𝟙_ _)).inv ≫ (q ⊗ₘ s)`. It is the node's specified m, and the left unitor
  is multiplication, sending `a ⊗ b` to `ab`. Both tensor and unitor are the
  existing localization/sheafification monoidal structure.
- The first conclusion is `Epi (etaleQuotientTensorGenerator ...)`.
  The rest supplies `e : F ⊗ G ≅ H` with `m ≫ e.hom = r`, together with
  `∀ f : F ⊗ G ⟶ H, m ≫ f = r → f = e.hom`. Thus existence and uniqueness refer
  to all morphisms, not just isomorphisms, and the resulting map is invertible.
- The local-section clause quantifies over every site object U and all sections
  a,b of the unit at U. `Functor.LaxMonoidal.μ (sheafToPresheaf ...) F G` is the
  canonical map from the sectionwise tensor to sections of the tensor sheaf. Its
  application to `q_U(a) ⊗ s_U(b)`, followed by `e_U`, is `r_U(ab)`. Here ab is
  written as the same canonical sectionwise tensor map for the two unit sheaves,
  followed by the left-unitor multiplication. This is the ring multiplication on
  A_T(U), so it covers locally constant a,b, not merely globally constant scalars.
- At a point in `E ∩ D`, for any three compatible normalized isomorphisms `iF`,
  `iG`, `iH`, the stalk tensorator followed by `stalk.map e.hom` and `iH.hom`
  sends `iF.inv a ⊗ iG.inv b` to `a * b`. The next equation says explicitly
  `stalk.map e.inv (iH.inv c) = μ (iF.inv c ⊗ iG.inv 1)`. These are exactly the
  stated multiplication map and its inverse c ↦ c tensor one.
- Outside the intersection the conclusion states `IsZero (stalk (F ⊗ G))`,
  `IsZero (stalk H)`, and `stalk.map e.hom = 0`. Between those zero objects this
  is the unique zero-to-zero morphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`, used through the published constant-scalar
  equivalence for the current encoding; no private module-sheaf definition.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtaleTopology`.
- `def-weil-size-convention` is a metatheoretic convention, with no declaration;
  explicit `universe u`, `Scheme.{u}`, and `ModuleCat.{u + 1}` implement it.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` and its exposed `CategoryTheory.exactFunctor`.
  The latter is the recorded option for this module-valued encoding.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalkDiagram`,
  `pointedEtaleStalk`, `pointedEtaleGerm`; the same stalk construction is used
  functorially through `Point.sheafFiber`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal` and its public tensor imports; the module-valued
  realization uses the existing `Etale.sheafMonoidalCategory`, definitionally
  `Sheaf.monoidalCategory`, and its ordinary sheafified tensor.
- Proof imports: `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
  (`etaleConstantModuleFunctor_isEquivalence`),
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
  (`exists_sheafificationTensorIso`, `nonempty_sheafTensorSheafificationIso`),
  `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
  (`etale_stalk_tensor_unique`),
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`moduleSheaves_colimits_forgetful`),
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
  (`isIso_of_isIso_sheafFiber_map`). The Mathlib proof dependencies are
  `SheafOfModules.instAbelian`, exactness of `Point.sheafFiber`,
  `Preadditive.epi_iff_isZero_cokernel'`, and `ShortComplex.Exact.gIsCokernel`.
  Their owning modules are imported directly or through these public imports.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf` supplies
  the canonical identification of the constant stalk;
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` supplies the underlying
  presheaf functor's lax tensor map for the section formula.

Source check: read `etale-cohomology.tex`, labels `lemma-stalk-exact` and
`theorem-exactness-stalks` (03PT, 03PU), and the final paragraph of
`main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-kunneth-supported.proof.md`.
The seven node proof steps are preserved in the theorem docstring. There is no
statement fault or disputed assertion.

Edge cases checked: empty T (stalk assumptions vacuous, sheaf category trivial),
zero A (all modules and all formulas zero, including 1 = 0), E or D empty,
disjoint E,D, E = D = all points, and points lying in exactly one subset. Off
intersection at least one tensor factor is zero; on intersection `c tensor 1`
is inverse to multiplication, also for the zero ring. No closedness of E,D or
nonempty-point assumption is introduced. Epimorphisms do not get replaced by
sectionwise surjections.

Searches actually run with `msearch.py N8 lem-pur-etale-quotient-tensor-stalk-criterion`:

- LeanFinder: "Tensor product of quotient module sheaves with stalks zero or the
  coefficient ring is the quotient on intersection support". Eight hits:
  algebraic `TensorProduct.quotTensorEquivQuotSMul*` identities, `QuotSMulTop`
  tensor quotients and module support. None is the sheaf-theoretic normalized
  stalk criterion.
- Loogle: `CategoryTheory.Sheaf, TensorProduct`. Zero hits.
- Mathlib grep: `quotient.*tensor|tensor.*quotient|stalk.*tensor|tensor.*stalk`
  in `Algebra/Category`. Zero hits.
- LeanSearch: "Tensor product quotient module sheaves zero or constant stalks
  normalized multiplication isomorphism". Eight algebraic quotient-tensor
  equivalences, including `TensorProduct.tensorQuotientEquiv` and
  `quotientTensorQuotientEquiv`; no module-sheaf criterion.
- `rg` over `lean/Sheaf`, `lean/WeilConjectures`, Mathlib and the upstream name
  index for the three proposed declaration names: no declarations with those
  names. Concept searches over project modules find `SupportQuotientProduct`
  and ordinary algebraic tensor quotients, not this general criterion.
  `grep -rn` for the item id in `lean/WeilConjectures` gives no hit.

Validation: prescribed `scompile.py` compiled both the isolated sandbox name and
actual module path cleanly, with no error or non-sorry warning. The first attempt
identified a missing public import for the existing lax monoidal structure of
`sheafToPresheaf`; the explicit owning-module import fixed it. No build of the
library and no direct mutation of the shared repository were run.

## Second reading by N8

A second clause-by-clause pass by the same worker (the dispatcher forbids starting
other agents and assigns independent delivery review to the maintainer) checked
both the copied node and the complete module. This is not claimed as an independent
agent review. The pass checked all three epic quotient maps, retained flatness,
all three normalized stalk assumptions, the canonical generator, epicity,
uniqueness among every morphism, invertibility, local sections, the multiplication
stalk and its specified inverse, and the off-support zero-to-zero map. The local
section formula uses the unit multiplication on all A_T(U) sections; replacing
that by the constant value A would have missed local sections. No mismatch or
statement change was found. The three declarations contain no auto-bound variables,
file-local notation, local instances, private definitions, or hollow data; the
only postponed proof is the named main theorem. The node changes only in `lean`.
