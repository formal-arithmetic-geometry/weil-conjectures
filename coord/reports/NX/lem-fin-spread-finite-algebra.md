## Worker report

The module `Sheaf.AlgebraicGeometry.SpreadFiniteAlgebra` states the two clauses of
`lem-fin-spread-finite-algebra` as `AlgebraicGeometry.spread_finite_algebra` and
`AlgebraicGeometry.spread_finite_algebra_product`. Both proofs are exactly `by sorry`.
No definitions, new nodes, dependency replacements, or statement corrections are needed.
The source read was the full blueprint file
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-fin-spread-finite-algebra.md`,
and the node's nine-step proof. Each theorem docstring carries the complete proof plan.

Hypotheses and clauses, checked against the node:

- A Noetherian domain: `(A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]`.
- Its fraction field: `(K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]`.
  This permits any chosen fraction field, without prescribing a particular construction.
- A projective morphism `T → Spec A`: `(T : Scheme.{u})
  (f : T ⟶ Spec (.of A)) [IsProjective f]`, using the recorded H-projective convention.
- Generic fibre `T_K`: `pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K)))`.
- A commutative unital structure-sheaf algebra: `C : T_K.CommAlgebraSheaf`.
- Finite coherent: `hC : RingedSpace.IsCoherent T_K.toRingedSpace C.toModule`.
  The recorded coherence predicate already includes finite type, so there is no redundant
  additional finiteness assumption.
- Some nonzero denominator: `∃ a : A, a ≠ 0 ∧ ...`.
- The localized base is exactly `Localization.Away a`, and the local scheme is the actual
  pullback of `f` along its canonical map to `Spec A`.
- The existential ring map `φ : Localization.Away a →+* K` satisfies
  `φ.comp (algebraMap A (Localization.Away a)) = algebraMap A K`.
  Localization's universal property fixes this map uniquely. The two equations on `g`
  fix the actual induced generic-to-local scheme morphism by its pullback projections.
  These data introduce the comparison morphism, rather than allowing an unrelated map.
- A finite algebra on that local scheme: `B : T_a.CommAlgebraSheaf`, with
  `B.toModule.IsQuasicoherent ∧ B.toModule.IsFiniteType`.
  Finiteness here is module finiteness, not algebra finite generation.
- Extension as an algebra, including multiplication and unit: a ring-sheaf map
  `θ : g⁻¹ B.right ⟶ C.right` for which
  `IsPushout (g⁻¹.map B.hom) (Scheme.Modules.tensorPullbackRingMap g) θ C.hom`.
  A pushout in commutative ring sheaves is the sheaf tensor product of algebras. Thus this
  is precisely `O_generic ⊗_{g⁻¹ O_local} g⁻¹ B ≅ C` as an algebra, with its structure map.
  It is not just an arbitrary underlying-module isomorphism. No pullback-algebra notion
  is redefined: the statement uses the existing general categorical universal property.
- A specified finite product decomposition: `(I : Type u) [Finite I]`, arbitrary algebra
  sheaves `Cs i`, projections `p : ∀ i, C ⟶ Cs i`, and
  `hp : IsLimit (Fan.mk C p)`. This describes the specified product cone, including its maps.
  No coherence assumption on the factors is added; they are retracts of the coherent C.
- Extended simultaneously: the second theorem has a single existential `a`, comparison
  `g`, algebra `B`, and map `θ`, then factors `Bs i`, projections `q`, and maps `θs`.
  `Nonempty (IsLimit (Fan.mk B q))` says the local cone is a product; every factor is
  quasi-coherent and of finite type; each `θs i` gives the same algebra scalar-extension
  pushout. Finally `g⁻¹.map (q i).right ≫ θs i = θ ≫ (p i).right` identifies each specified
  generic projection. Thus the given decomposition, not merely some abstract factorization,
  is extended at the same localization.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention node without a declaration:
  `Scheme`, `Spec`, and scheme morphisms are the standard Mathlib ones.
- `def-pc-projective-morphism`: `AlgebraicGeometry.IsProjective` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`. Its full source and docstrings
  were read on the server's read-only live tree because this extracted module is absent
  from the older local upstream source. It extends `IsHProjective f` and `QuasiCompact f`.
  The required module and declaration were verified by a server compilation probe.
- `pqf-def-coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `Sheaf.AlgebraicGeometry.Coherent`, with its finite-type clause and kernels on opens.
- `def-weil-pbc-comm-algebra-sheaf`: `AlgebraicGeometry.Scheme.CommAlgebraSheaf` and
  `.toModule` from `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`, using the actual under
  category of the structure sheaf and its prescribed underlying module.
- `def-weil-ring-localization-away`: `Localization.Away` from
  `Mathlib.GroupTheory.MonoidLocalization.Away`, the localization at powers of `a`;
  ring structure supplied by `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-pc-base-change`: `pullback`, `pullback.fst`, `pullback.snd` as recorded in
  `Sheaf.AlgebraicGeometry.BaseChangeConventions`. This module is imported publicly.
  Its `moduleBaseChange` is only the module variant, and is not misused as algebra pullback.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, exactly Noetherian as a module over itself.
- The inverse image is the recorded `TopCat.Sheaf.inverseImageConstruction` from
  `Sheaf.Topology.InverseImageModule`; the structure map is
  `Scheme.Modules.tensorPullbackRingMap` from `Sheaf.AlgebraicGeometry.TensorPullback`.
  These are reached through the public base-change import, not copied.
- Every proof dependency with a recorded module is imported (proof-only imports are not
  public). Mathlib leaves without module records are provided by those imports.

Edge cases checked: `I` can be empty, making the fans terminal and the generic and extended
algebras zero; the zero algebra extends already at `a = 1`. Zero factors and empty T are
allowed. No nonzero or positive-rank hypotheses are imposed on C or any factor. If A is
already a field, one can choose `a = 1`. No flatness, integrality of T, dominance, reducedness,
or nonempty generic-fibre assumption is used. The field characteristic is unrestricted.
All finite index sets have representatives in `Type u`; no independent smaller universe
is used for test objects. Every universe and variable is explicitly bound.

Searches made before writing:

- `msearch.py ... leanfinder` query: "A finite coherent algebra on the generic fibre of a
  projective scheme over a Noetherian domain extends after inverting a nonzero element,
  with finite product decomposition". Eight hits about projective spectra, finite-type
  localization, global sections of proper schemes and quasi-finiteness; none states this.
- `msearch.py ... loogle` query: `IsFractionRing, IsProjective, IsCoherent`.
  Zero hits; the Mathlib-only service does not know the project's `IsProjective`.
- `msearch.py ... grep` query: `spread|descend.*[Aa]lgebra`, Mathlib subdirectory
  `AlgebraicGeometry`. Ten hits in SpreadingOut and Birational/RationalMap, about spreading
  individual morphisms, not an algebra sheaf over the whole generic fibre.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for spreading/descent of
  algebras and for the proposed declaration names: no identical statement or name.
  GenericFiniteAlgebraSplitting is the different base-ring splitting statement; the
  FiniteGenericCurveModel module only cites this node as a future proof dependency.
- `grep -rn lem-fin-spread-finite-algebra` in upstream `WeilConjectures`: no match.
  The upstream name inventory also has no proposed-name collision.

Validation: the final module compiled cleanly on the server with scompile.py (5.9 seconds,
nice 19, two threads, 60-second file limit); no errors or warnings. No local Lean compiler
or global build was run. There are no STATEMENT-DISPUTED flags or node faults.

## Second reading by NX

I independently read the node, its seven statement-dependency nodes and their declarations,
the complete blueprint source at sec-smooth-purity/sk-prop-sf-cbc/
lem-fin-spread-finite-algebra.md, and Stacks limits.tex,
lemma-descend-modules-finite-presentation (Tag 01ZR), including all three clauses and its
surrounding hypotheses. The blueprint supplies the Noetherian-domain and projectivity
hypotheses; 01ZR supplies the affine-transition, qcqs finite-presentation descent tool,
not an extra hypothesis on the algebra. No statement correction is present or needed.

The node's objects, hypotheses and conclusion, matched clause by clause:

1. A Noetherian domain A: `(A : Type u) [CommRing A] [IsDomain A]
   [IsNoetherianRing A]`. Exact. IsNoetherianRing is Noetherian as its own module,
   equivalently every ideal is finitely generated; the domain is nontrivial as required.
2. Its fraction field K: `(K : Type u) [Field K] [Algebra A K]
   [IsFractionRing A K]`. Exact; this is any chosen fraction field, not a finite
   extension or a special characteristic.
3. A projective morphism T to Spec A: `(T : Scheme.{u})
   (f : T ⟶ Spec (.of A)) [IsProjective f]`. Exact under the dependency's explicit
   H-projective convention. I read the extracted Morphisms.Projective module on the
   server's read-only live tree: IsHProjective is a closed projective-space embedding,
   and IsProjective extends it and QuasiCompact, exactly the recorded notion.
4. The generic fibre T_K: `pullback f (Spec.map (CommRingCat.ofHom
   (algebraMap A K)))`. Exact scheme-theoretic base change, using the recorded
   BaseChangeConventions pullback and its two projections.
5. A finite coherent commutative unital O_(T_K)-algebra: `C : T_K.CommAlgebraSheaf`
   and `hC : RingedSpace.IsCoherent T_K.toRingedSpace C.toModule`. Exact. I read
   CommAlgebraSheaf = Under X.sheaf and its toModule construction (rank one over itself,
   restriction of scalars); IsCoherent includes IsFiniteType and finite-type kernels
   on every open. Thus finiteness is not omitted or replaced by finite algebra generation.
6. Existence after one nonzero principal localization: `∃ (a : A), a ≠ 0 ∧ ...`,
   base ring `Localization.Away a`, and local scheme the actual pullback along its
   algebraMap. Exact. Away is localization at Submonoid.powers a, as its recorded
   Mathlib declaration says, with ring structure from Localization.Away.Basic.
7. The generic-to-local comparison: existential `φ : Localization.Away a →+* K`
   satisfying `φ.comp (algebraMap A (Localization.Away a)) = algebraMap A K`, and
   `g` with both prescribed projection equations. Exact auxiliary data: the localization
   universal property uniquely fixes φ and pullback hom-extensionality uniquely fixes g.
   These equations specify the comparison meant by extension; they impose no extra
   geometric hypothesis and do not permit an unrelated morphism.
8. A finite algebra B on the localized scheme: its CommAlgebraSheaf binder and
   `B.toModule.IsQuasicoherent ∧ B.toModule.IsFiniteType`. Exact finite quasi-coherent
   algebra, not merely a finite-type algebra. No flatness, locally free or positive-rank
   requirement is added.
9. Extension of C as an algebra: θ is a morphism of inverse-image commutative ring
   sheaves, and `IsPushout (inverseImageConstruction.map B.hom)
   (Scheme.Modules.tensorPullbackRingMap g) θ C.hom`. Exact. I read the actual
   inverseImageConstruction, tensorPullbackRingMap and Mathlib IsPushout declarations:
   this is the cocartesian square from g⁻¹ O_local, with targets g⁻¹ B and O_generic,
   and vertex C. In commutative ring sheaves it is the sheaf tensor product, including
   its O_generic structure map, hence precisely an algebra scalar-extension identification.
10. A specified finite product decomposition: in spread_finite_algebra_product,
    `(I : Type u) [Finite I]`, `Cs`, projections `p : ∀ i, C ⟶ Cs i`, and
    `hp : IsLimit (Fan.mk C p)`. Exact given product cone; no independent coherence
    hypothesis on factors is assumed. Finite factors inherit finiteness from the product.
11. Simultaneous extension at the same localization: the second theorem first chooses
    the single a, φ, g, B, θ with the same clauses, then chooses Bs, q and θs.
    `Nonempty (IsLimit (Fan.mk B q))` is the descended product cone; each Bs is
    quasi-coherent finite type; each θs gives its scalar-extension pushout; and
    `inverseImageConstruction.map (q i).right ≫ θs i = θ ≫ (p i).right`
    identifies each specified generic projection. Exact, including the order of choices
    and the compatibility with the given decomposition.

Edge cases: empty I is allowed (no Nonempty or Fintype binder), and its fan is terminal,
so the zero algebra extends with a = 1. Zero algebra, zero factors and empty T are allowed;
no Nontrivial condition on algebra sections occurs. Projective space permits n = 0 and
no dimension bound on T is imposed. A already a field allows a = 1. Characteristics are
unrestricted; no dominance, reducedness, integrality of T or nonempty generic fibre is
assumed. The arbitrary common universe u is explicit throughout; finite index types in
Type u represent all finite products, with no smaller test-object universe. All variables
and universes are bound, with autoImplicit false and no local notation or local instances.

Independent searches (different queries from the worker):

- LeanSearch: "A finite coherent sheaf of commutative algebras on the generic fiber of a
  projective scheme over a Noetherian integral domain extends over a principal open subset".
  The service returned Internal Server Error; this is recorded as unavailable, no verdict.
- LeanFinder: "A coherent sheaf of finite commutative algebras over a fraction field descends
  to a principal open of the base". Eight hits about local fraction representatives and
  basic-open section rings, none about spreading an algebra sheaf on a projective scheme.
- Loogle: `IsFractionRing, Localization.Away`. Zero hits.
- Recorded Mathlib grep: `generic.*algebra|algebra.*generic|descend.*coherent` in
  AlgebraicGeometry. One irrelevant Smooth.lean stalk-map hit.
- Independently rg-searched `spread.*algebra|algebra.*spread|descend.*algebra|algebra.*descend`
  in upstream WeilConjectures, project lean/Sheaf and Mathlib AlgebraicGeometry.
  Faithfully flat algebra descent, finite etale stage descent and generic base-ring
  splitting are different statements. Opened GenericFiniteAlgebraSplitting: it splits a
  given finite base-ring algebra after etale base change, not a generic algebra sheaf over T.
  Neither proposed full name occurs in Mathlib, upstream, the project, or the upstream
  name inventory. No existing exact statement was found.

There are no new definition nodes or dependency modules in the delivery. Every recorded
statement dependency is usable; no missing notion, substitute object or private definition
is needed. Checked all recorded proof-dependency module paths against the imports: all are
included, publicly for notions used by the signature and non-publicly for proof-only tools.
Both theorem docstrings contain the source, blueprint id and all nine proof steps; both
proofs are exactly `by sorry`, with no additional declaration or hollow definition.

Mismatches found: none. I preserved the Lean module and the node record. The stored
lean.statement matches the primary declaration's signature verbatim. The only change is
this second-reading report and the independently recorded searches.

Validation: scompile.py compiled the complete delivered module on the server in 5.8 seconds,
nice 19, two threads, limit 60 seconds, without errors or warnings. No local compilation,
Lake build, upstream modification or direct repository git command was run.
