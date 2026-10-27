## Worker report

The delivery states `AlgebraicGeometry.finiteFlatAffineGroupoid_moduli` in
`Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli`. It also supplies the missing
presentation notion in `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`.
The original statement, source and nine-step proof are unchanged. The item gains the
new definition node and the already landed stack-point-topology and scheme-space nodes.
There is one postponed theorem, `finiteFlatAffineGroupoid_moduli`; its docstring carries
all nine proof steps. All definitions have explicit data, with no postponed proof fields.

Sources read: `stacks-more-morphisms.tex`, Tags 0DUM, 0DUP and 0DUR (the well-nigh-affine
presentation, invariant-spectrum construction and its uniform categorical property);
`groupoids.tex`, Tags 03BK and 03BL (flat invariant base change and geometric orbits);
`spaces-groupoids.tex`, Tags 044Q, 044R and 044T (quotient stack, original arrows and
composition cocycle); `stacks.tex` stackification as exported by the recorded local-
description declaration, Tags 02ZP and 0436. The latest blueprint is the current
`literature/blueprint/latest` convention. The inherited `blueprint.from.node` is null:
`tools/blueprint_refs.py ancestor lem-sfb-finite-flat-affine-groupoid-moduli` returned
None. Its explicit inherited blueprint anchor is
`det-thm-sf-ctf-stability-direct-images`, proof (3), the alteration/moduli prerequisite.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- The two affine k-schemes: `E L : Type u`, their commutative-ring and k-algebra
  instances, and `Spec (.of E)`, `Spec (.of L)` with Mathlib's `asOver (Spec (.of k))`.
  There is no finite-type hypothesis. Empty spectra are permitted.
- The k-morphisms s,t: `σ τ : E →ₐ[k] L`, contravariantly via `Spec.map` and `asOver`.
  This represents all morphisms of the specified affine k-schemes.
- The specified e,i,c: the three scheme-map binders. Their groupoid identities are
  precisely `P.groupoid : Scheme.IsGroupoid ...`, the recorded dependency's predicate.
  Source, target and composition have the source's orientation c(q,r)=q after r.
- Finite locally free s,t: the two `.IsFiniteLocallyFree` instances, whose recorded
  upstream class extends finite, flat and locally of finite presentation. No degree,
  nonempty, reducedness or etaleness assumption is imposed.
- Z=[U/R]: `F`, `a` and `P : SchemeGroupoidQuotientPresentation ... F a` name an arbitrary
  presentation of this quotient, rather than selecting an unknown object by choice.
  P includes fppf descent, local lifting, the natural isomorphism identifying original
  arrows with all isomorphisms between lifted objects, and its composition cocycle.
  This presents the fppf stackification up to equivalence; its algebraicity is the
  conclusion `∃ hF : IsAlgebraicModuliStack F`, not an additional hypothesis.
- Invariant ring C: the existing `AlgHom.equalizer σ τ`, with underlying subset exactly
  `{a | σ a = τ a}`. Its k-algebra structure is inherited by Mathlib. The instance
  `affineGroupoidInvariantArrowAlgebra` uses σ on L; τ agrees there by the equalizer
  property, as used in `affineGroupoidInvariantTarget`.
- M=Spec C: `affineGroupoidModuliBase σ τ`, including the inherited structure over k.
- Canonical f: the existential based functor f, with
  `a.comp f = discreteModuliMap (yoneda.map (affineGroupoidModuliAtlasMap σ τ))`.
  The latter map is Spec of the actual inclusion C→E. Categoricity below determines
  this descended morphism uniquely.
- Quasi-compact and quasi-separated: the existing
  `IsQuasiCompactAlgebraicModuliMap` and `IsQuasiSeparatedAlgebraicModuliMap` predicates,
  as used by the recorded adequate-moduli definition. They test the actual 2-fibre
  products and relative diagonal. These are the general algebraic-stack predicates;
  the etale-atlas-only DM predicates are not substituted.
- Uniform categorical: for every algebraic space B and map b:B→M, the hypothesis on
  every representable etale chart T→B is exactly chartwise flatness of B→M. For every
  algebraic space Y, the stated `Function.Bijective` sends h:B→Y to its composite
  with the actual first projection of `B ×_M F`. It ranges over all algebraic-space
  targets and flat space bases, not just affine targets or affine bases.
- Universal homeomorphism: for every algebraic stack Z and map g:Z→M,
  `IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f))`. These are the original
  field-object quotient point sets, with the recorded final topology over all smooth
  surjective scheme atlases. The Z universes contain both endpoints and arbitrary
  extra v',w'; they are not forced equal to F's universes.
- Geometric points: every algebraically closed Ω and field homomorphism j:k→Ω has the
  `Function.Bijective` map on skeleton objects of `moduliFiberMap f` at Spec Ω.
  Skeleton objects are precisely fibrewise isomorphism classes, while the target
  is the discrete fibre M(Ω). This uses the inherited scheme-universe convention;
  enlarging u accommodates arbitrary extensions, as for the recorded coarse-moduli
  predicate. No algebraicity of Ω over k is required.
- O_M→f_*O_F: `IsIso (moduliStructureMap hF.1.1 (schemeSpace M) f)`, the recorded
  canonical regular-function pullback map, with its canonical ULift transport.
- Every flat affine base change: D is any commutative C-algebra and
  `[Module.Flat C D]`. The source and target tensor maps are
  `Algebra.TensorProduct.map` of the two actual C-algebra coordinate maps and id_D.
  Injectivity of `includeRight : D →ₐ[C] E ⊗[C] D`, together with the displayed
  equivalence between their equalizer and its image, states that the equalizer is
  exactly D under d↦1⊗d, including uniqueness of this scalar identification.
- Global functions on this base change: `affineGroupoidModuliBaseChange` is the actual
  iso-comma 2-fibre product, retaining the specified comparison isomorphism. The last
  clause says every compatible family of regular functions has a unique d whose
  structural pullbacks equal that family on every object. Its `RingCat.sectionsSubring`
  is literally the ring used by `moduliGlobalSectionsRing (moduliStructureSheaf ...)`;
  the latter sheaf's underlying presheaf is `moduliStructurePresheaf`. Thus this states
  the canonical identification with D, not an unrelated abstract ring equivalence.
  `moduliAffineFunctionValue` explicitly pulls back d using ΓSpecIso and the scheme
  map supplied by the first projection. Compatibility of these pullbacks is ordinary
  functoriality of Γ; ring operations on compatible families are pointwise.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`;
  `GammaSpecAdjunction`: `Scheme.ΓSpecIso` and the affine spectrum correspondence.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`, including all
  identity, inverse and associativity fields.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` (lines 894–909 of the current checkout).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology` and its flat locally
  finitely presented covering families; `Mathlib.CategoryTheory.Sites.Over` supplies
  the big fppf site over the base.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, `Flat.iff_flat_stalkMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its chart predicates
  `IsEtale`, and `EtaleSite`; `EnlargedEtaleRingedSite`: `schemeSpace`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory` interfaces,
  `IsFibredInGroupoids`, `discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst` and `moduliFiberMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: both general qcqs predicates.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`: `moduliStructurePresheaf`,
  `moduliStructureSheaf`, `moduliGlobalSectionsRing`, `moduliStructureMap`.
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`: `IsAdequateModuliSpace` was read to
  identify the exact shared qcqs and structure-map conventions. Adequacy itself is
  neither a hypothesis nor an asserted extra conclusion of this item.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `moduliPointTopologicalSpace`; its point quotient is `ModuliPoints` and the map is
  `moduliPointMap` from the recorded `DmStackMorphismProperties` interface. The point
  topology here is the smooth-atlas topology, not that file's DM closed-set predicate.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `.AlgebraicClosure`: `IsAlgClosed`,
  `AlgebraicClosure`. The geometric-point condition uses `IsAlgClosed`, not `IsAlgClosure`.

The module imports every available recorded proof-dependency module, privately where
only the proof needs it, and the Mathlib modules of the recorded Mathlib matches.
Seven proof nodes have no Lean declaration yet: affine-groupoid-quasicoherent-algebra-
descent, algebraic-stack-fibre-products, flat-groupoid-quotient-open-presentation,
fppf-groupoid-stack-presentations, locally-free-groupoid-invariant-affine,
representable-stack-fppf-locality and separated-lqf-affine-finite-set (all with prefix
`lem-sfb-`). They are proof prerequisites only and no notion is copied from their proofs.

Searches actually run:

- msearch leanfinder: "Finite locally free affine scheme groupoid quotient stack
  invariant spectrum uniform categorical universal homeomorphism". Eight hits,
  including affine schemes and finite-morphism criteria; no exact theorem.
- msearch loogle: "AlgebraicGeometry.Scheme.IsGroupoid,
  CategoryTheory.IsAlgebraicModuliStack". Zero hits; Loogle does not index the project
  declaration `AlgebraicGeometry.Scheme.IsGroupoid` (unknown identifier).
- msearch grep: `groupoid.*moduli|uniformCategorical|UniformCategorical`. Zero Mathlib hits.
- msearch leansearch: "fppf stack quotient scheme groupoid presentation". Eight hits
  on generic pseudofunctor stack descent and ordinary groupoids, not this presentation.
- msearch leanfinder: "fppf stack quotient scheme groupoid presentation preserving
  arrows and composition". Eight generic IsStack/IsPrestack descent hits, no presentation.
- msearch grep: `quotient.*[Pp]resentation|[Ff]ppf.*[Qq]uotient|IsGroupoid`, CategoryTheory.
  Twenty generic groupoid hits, none representing the quotient of a scheme groupoid.
- rg in `lean/WeilConjectures` for the item id and for groupoid/quotient combinations:
  no matching theorem or generic quotient presentation. rg in `lean/Sheaf` found the
  action-specific torsor quotient, the orbit sheaf quotient, and generic pseudofunctor
  stackification, none giving this scheme-groupoid presentation. Reused their shared
  fibred-category, point, structure-sheaf and scheme-space notions.
- DAG grep found no definition node carrying this generic presentation. The adjacent
  fppf-presentation theorem nodes have no usable declaration; they assert algebraicity
  and geometric properties rather than defining this input presentation.
- `tools/blueprint_refs.py search 'groupoid quotient stack'`: zero blueprint nodes.
  The ancestor query returned None, as already explained in the inherited item.

Edge cases checked mathematically: E=L=0 (empty atlas and empty quotient), identity
relation R=U (C=E, f=id), a finite group scheme over a point (BG→Spec k), the nonetale
example μ_p in characteristic p, nonreduced rings, disconnected bases of variable
rank, D=0 and identity base change D=C. No nonempty or constant-rank condition occurs.
For a finite groupoid cover, identities imply any fibre used to lift an existing
object is nonempty, without excluding the empty overall quotient. General algebraic
spaces and arbitrary algebraic-stack base changes are explicitly quantified.

Validation: both modules compiled separately in dependency order through scompile.py,
in both sandbox and library modes; only the expected postponed theorem is present.
No statement correction or STATEMENT-DISPUTED issue was needed. The dry run first
found two long docstring lines, which were wrapped, and then required `import_flags`
on the new node. The current `tools/stage2_delivery.py` schema (updated 2026-10-23)
requires that key; the new node now has `import_flags: []`. No tool was modified.

## New nodes

`def-sfb-scheme-groupoid-quotient-presentation` defines the fppf quotient presentation
with original arrow bijections and composition, from Stacks 044Q, 044R, 044T, 02ZP,
0436. It uses the existing scheme groupoid laws and fibred-category conventions.
It has its own module and one transport helper, with no `sorry`. It does not assert
algebraicity, finite freeness, moduli properties or a choice of quotient object.
Generic pseudofunctor stackification alone does not provide this scheme-groupoid
interface; action-group torsors and orbit sheaves are different notions. The new
node records the actual outputs of the LeanSearch, LeanFinder and Mathlib grep calls;
DAG, upstream and project searches above found no existing owner. Its null blueprint
ancestor follows the actual ancestor command and retains the inherited explicit anchor.

## Second reading by Q50

A separate rereading checked the source, node, new definition and compiled signatures.
This is the worker's second pass; the maintainer supplies the independent review.
The orientation of c was checked against r:x→y followed by q:y→z: the first pullback
projection is q and the second is r. The presentation's arrow bijection includes all
vertical arrows, with the actual isomorphism and the original composition, so it
cannot silently replace a nontrivial stabilizer by an orbit sheaf. Algebraicity is
concluded. The categorical map is composition with the indicated projection after
arbitrary flat space bases. The universal homeomorphism uses the smooth-atlas point
topology after arbitrary stack bases. Both tensor endpoint maps use the same C-action,
and the target's C-linearity is exactly the invariant equality. The function-ring
clause uses structural pullback and compatible families rather than an unconstrained
isomorphism. The only correction made during implementation was to use the proper
quotient-stack source tags 044Q/044R/044T instead of the smooth-groupoid theorem tag
04TK in the new definition's docstrings. There is no change to the item's statement.
