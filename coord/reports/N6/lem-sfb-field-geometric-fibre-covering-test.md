## Worker report

The module `Sheaf.Paper.FieldGeometricFibreCoveringTest` states
`AlgebraicGeometry.ProEtale.field_geometric_fibre_covering_test`, with proof `sorry`.
It introduces no declaration other than this theorem, no replacement definitions,
no new nodes, and no change to the natural-language statement. The restriction
topologies are explicit terms in the two `@IsHomeomorph` assertions. Their infima
range over **all** finite etale subalgebras. In each term the target topology `⊥`
is the discrete topology on the finite-stage Hom set. Thus the topology is the
specified initial topology for restriction, without making an additional choice
of stages or using a topology on Ω.

Hypothesis and clause correspondence:

- A field k, its separable closure Ω, and an ind-etale k-algebra B are
  `(k : Type u) (Ω : Type v) (B : Type w) [Field k] [Field Ω] [Algebra k Ω]
  [IsSepClosure k Ω] [CommRing B] [Algebra k B]` and
  `hB : RingHom.IndEtaleAcrossUniverses (algebraMap k B)`.
- The size convention is explicit universe polymorphism: the field, closure,
  algebra and family-index universes are independently bound as `u v w t`.
  Sources and targets of scheme families share the chosen scheme bound `w`;
  the tensor ring lives in `max v w`. No equality of coefficient and scheme
  universes, finiteness of the family, or nonemptiness is assumed.
- `B_Ω` is exactly `Ω ⊗[k] B`, with its canonical Ω-algebra structure, and its
  asserted ind-etaleness is the first conjunct using the recorded
  `RingHom.IndEtaleAcrossUniverses`.
- Every point's canonical residue-field identification is
  `∀ q : PrimeSpectrum (Ω ⊗[k] B), Function.Bijective
  (algebraMap Ω q.asIdeal.ResidueField)`. Bijectivity of this **structural map**
  is precisely a canonical Ω-algebra isomorphism, stronger in normalization
  than a bare unspecified ring equivalence and equivalent to the node's clause.
- `F_k(B)` is exactly `B →ₐ[k] Ω`. Its topology is the infimum, over
  `D : Subalgebra k B`, `Module.Finite k D` and `Algebra.Etale k D`, of
  `TopologicalSpace.induced (fun f ↦ f.comp D.val) ⊥`.
- `AlgHom.liftEquiv k Ω B Ω` is the existing tensor universal-property
  equivalence. Its forward map sends `a ⊗ b` to `a * f b`, by
  `AlgHom.liftEquiv_tmul`. The map in the first `IsHomeomorph` is
  `PrimeSpectrum.comap ((AlgHom.liftEquiv k Ω B Ω) f).toRingHom ⊥`.
  Its ideal is exactly the kernel, and `PrimeSpectrum (Ω ⊗[k] B)` is the
  underlying topological space of `Spec (.of (Ω ⊗[k] B))`.
- The second `IsHomeomorph` has source `(Ω ⊗[k] B) →ₐ[Ω] Ω`, equipped with
  the identical finite-etale-subalgebra topology over Ω. Its map is
  `(AlgHom.liftEquiv k Ω B Ω).symm`, which is exactly restriction along
  `b ↦ 1 ⊗ b`, by `AlgHom.liftEquiv_symm_apply`. Its target is the same
  `F_k(B)` topology. These are underlying spaces, as the node expressly
  forgets the G-action in this comparison. The preamble's action is the
  usual postcomposition by `Ω ≃ₐ[k] Ω`; no extra equivariance claim for the
  spectrum identification is imposed.
- Naturality for all k-algebra maps `α : B →ₐ[k] D` between ind-etale algebras
  is the next conjunct. The first equation contracts the kernel along the
  **canonical** `Algebra.TensorProduct.map (AlgHom.id Ω Ω) α`, not an
  arbitrary map between the tensor rings. The second equation commutes
  restriction with precomposition by that same tensor map. Their directions
  are `F_k(D) → F_k(B)` and `Spec D_Ω → Spec B_Ω`.
- An arbitrary small family is `I : Type t`, `Ba : I → Type w`, with
  commutative-ring and k-algebra instances for every `Ba a`, maps
  `α : ∀ a, B →ₐ[k] Ba a`, and ind-etaleness for every member.
- Its scheme family is exactly
  `Presieve.ofArrows (fun a ↦ Spec (.of (Ba a)))
  (fun a ↦ Spec.map (CommRingCat.ofHom (α a).toRingHom))`.
  Fpqc covering means membership in the recorded
  `Scheme.fpqcPrecoverage (Spec (.of B))`.
- The iff's other side is `∃ J : Finset I, ∀ f : B →ₐ[k] Ω,
  ∃ a ∈ J, ∃ g : Ba a →ₐ[k] Ω, g.comp (α a) = f`: exactly a finite
  subfamily whose precomposition maps are jointly surjective. No per-member
  quasi-compactness or surjectivity is added.
- The same theorem specializes to `k = Ω` using
  `IsSepClosure.self_of_isSepClosed`; the Ω-based topology already appears
  explicitly in the restriction homeomorphism. Separably closed imperfect
  fields are allowed: no algebraic closedness or perfection is assumed.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem` and its underlying Mathlib
  `IsSepClosure`, whose fields are separable closedness and separability.
- `def-weil-size-convention` is a metatheoretic convention, without a
  declaration or module. All universes are explicitly bound.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`, defined as the existing ind-etale
  predicate on the canonical `RingHom.ulift` to a common universe.
  Its public `IndPrincipalZariski` import exposes the original notions.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`, publicly
  available through the fpqc/pullback imports. The underlying space of Spec
  is definitionally `PrimeSpectrum`, so no different spectrum is introduced.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`
  and its projections, publicly available through
  `Mathlib.AlgebraicGeometry.Pullbacks`. Fibre products enter the proof plan;
  the affine ring is stated directly as the canonical tensor product.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`;
  the recorded Mathlib match identifies its family condition with the node's
  affine-open definition, including empty families over the empty scheme.
- `Mathlib.RingTheory.TensorProduct.Basic` (via `.Maps`):
  `AlgHom.liftEquiv`, its pure-tensor and restriction formulas;
  `Algebra.TensorProduct.map` for the specified naturality maps.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField` and its canonical Ω-algebra structure.
- `Mathlib.Topology.Homeomorph.Lemmas`: `IsHomeomorph`, asserting that the
  **specified function** is a homeomorphism, equivalent to an existential
  homeomorphism whose forward function is that one.

Stated proof dependencies are imported privately: `IndEtaleStability`,
`CondensedPointBasis`, `SpecFiniteProductFields`,
`FilteredSpectrumTopologicalLimit`, Mathlib `WeaklyEtale`, `OpenImmersion`,
`PullbackCarrier`, and the already public fpqc/pullback modules.
`lem-sfb-field-geometric-fibre-construction` has no Lean record in the read
repository. It is a proof dependency, not a needed new input/interface:
this module writes the topologies directly as real terms and uses the existing
`AlgHom.liftEquiv`. Thus no unrecorded data or postponed construction is
required for the statement. Its full theorem is not copied or approximated.
The docstring includes all eight proof steps, for later implementation.

Edge cases checked before writing:

- B zero: there are no unital maps to Ω or points of its split spectrum;
  both homeomorphisms are maps of empty spaces and the residue clause is
  vacuous. The empty finite subfamily makes the covering iff true.
- Empty I with nonzero B: the geometric fibre is nonempty (finite-stage
  construction), so joint surjectivity fails, as does fpqc covering.
- A zero source contributes no geometric points, and is permitted by
  `[CommRing (Ba a)]`, with no `Nontrivial` binder.
- B = k gives one geometric point and a split spectrum with residue Ω.
- Finite products, including the product with zero factors, give the
  coordinate-kernel maps and include all disconnected cases.
- Non-Galois finite separable field algebras are included, as are imperfect
  separably closed base fields and uncountable index types.
- k = Ω follows by the existing self-separable-closure instance.

Searches actually run (logged by msearch.py in searches.jsonl):

1. `leanfinder`: "For ind etale algebras over a field the geometric fibre Hom
   into a separable closure is homeomorphic to the spectrum after base
   change, and fpqc coverings correspond to finite jointly surjective
   subfamilies". Eight hits, including purely inseparable spectrum
   homeomorphisms and finite etale product classification; no full match.
2. `loogle`: "PrimeSpectrum.comap, Algebra.TensorProduct.lift, Homeomorph".
   One hit, `PrimeSpectrum.coe_preimageHomeomorphFiber_apply_asIdeal`;
   it concerns a prime's ring-theoretic fibre, not this geometric Hom space.
3. `grep` via msearch.py:
   "AlgHom.*(topology|TopologicalSpace)|fpqc.*(finite|surjective)|indEtale".
   Five hits: fpqc precoverage and continuous-map algebra APIs, no full match.
4. `leanfinder`: "The topology of pointwise convergence on algebra
   homomorphisms into a discrete field equals restriction to finite
   subalgebras". Eight hits, including CommRingCat.HomTopology and Krull
   limit continuity; none provides the complete node statement.
5. `leansearch`: "Geometric points of an ind etale algebra over a field
   identify with its spectrum after tensoring with a separable closure and
   detect fpqc covering families". Eight hits, principally finite etale
   product classification and etale loci; no full match.
6. `rg` in the specified `lean/WeilConjectures` and `lean/Sheaf` trees for
   the item id and `finiteEtaleSub|finiteEtale.*[Tt]opology|
   fieldGeometricFibre|fieldGeometricFiber|indEtale.*[Ff]iber|
   indEtale.*[Ff]ibre|geometric-fibre-construction`. The finite-subalgebra
   union and the parent `FieldProfiniteGaloisSite` are related, but neither
   states this node or defines its Hom-space restriction topology. Read
   both modules: the parent's theorem is an existential site equivalence,
   without a normalized pointwise fibre construction or covering test of
   this exact family. Existing etale geometric-point APIs are finite/discrete.

Source read directly: Bhatt--Scholze PDF pp. 27--28, Definition 4.1.1 and
Examples 4.1.4 and 4.1.10. No source correction or disputed statement found.
Validation: scompile.py compiled both sandbox and library names cleanly;
only the required theorem proof is postponed.

## Second reading by N6

A separate second pass in this worker compared the node and the finished
signature clause by clause. Independent maintainer review follows delivery.
The two topology expressions use all finite etale subalgebras; the structural
residue map fixes the canonical identification; extension is Mathlib's actual
tensor extension; the spectrum map is contraction of the zero prime; both
naturality equations have the correct contravariant direction. The family is
unrestricted, and the finite subset is a conclusion. There is no nonempty,
nonzero, algebraically closed, finite-family or individual-surjectivity
hypothesis. The Ω-based topology uses Ω as the base, and the self-closure
specialization remains available. On this pass, replaced the initial local
`letI` topology binders by explicit topology arguments to `@IsHomeomorph`,
following the brief's instruction against let-bindings in statements. The
revised file was recompiled. No mathematical mismatch remains.
