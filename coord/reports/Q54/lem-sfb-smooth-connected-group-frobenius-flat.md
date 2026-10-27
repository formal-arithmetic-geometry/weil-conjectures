## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothConnectedGroupFrobeniusFlat` states
`AlgebraicGeometry.smoothConnectedGroup_relativeIterateFrobenius_finite_faithfullyFlat`.
Its proof is exactly `sorry`. The only other declaration,
`AlgebraicGeometry.groupRelativeIterateFrobenius`, is a real construction bundling
upstream `Scheme.relativeIterateFrobenius` as a morphism in `Over (Spec k)` using
upstream `Scheme.relativeIterateFrobenius_snd`. It chooses no maps or group laws.
No new independent notion, dependency repair, or statement correction is needed.

Hypothesis and clause correspondence:

- An algebraically closed field `k` is `(k : Type u) [Field k] [IsAlgClosed k]`.
- Prime characteristic `p > 0` is `(p : ℕ) [CharP k p] (hp : p.Prime)`.
  Primality entails strict positivity, including `p = 2`.
- A `k`-group scheme is `G : Over (Spec (.of k))` with `[GrpObj G]`.
  The specified base is part of the object, and its structure morphism is `G.hom`.
- Affine and connected are `[IsAffine G.left] [ConnectedSpace G.left]`.
  Mathlib's connectedness includes nonemptiness, as does the recorded dependency.
- Smoothness is `[Smooth G.hom]`. Finite type is explicitly the dependency's
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` conjunction.
- `r ≥ 1` is `(r : ℕ) (hr : 1 ≤ r)` and `q` is written `p ^ r` throughout.
- The coordinate algebra `C = k[G]` is `Γ(G.left, ⊤)`.
- The Frobenius twist is
  `(Over.pullback ((Spec (.of k)).iterateFrobenius hp h r)).obj G`, where
  `h = Scheme.isOfCharacteristic_Spec (CharP.cast_eq_zero k p)`.
  `Over.pullback` is defined as `Over.mk (pullback.snd G.hom F)` and therefore
  uses the second-factor `k`-structure. Stacks 0CCG and Milne 2.26 identify this
  exact pullback with `Spec (C ⊗_{k, a ↦ a^q} k)`.
- The target group structure is the existing image of `[GrpObj G]` under this
  pullback functor: `CategoryTheory.Functor.grpObjObj`, enabled by the global
  scoped `CategoryTheory.Obj` instances. The functor is monoidal by the existing
  `Over.pullback` instance in `Monoidal.Cartesian.Over`. Thus its operations
  are the base-changed operations of the specified `G`, never an existential
  group structure or an assumed homomorphism.
- `groupRelativeIterateFrobenius ...` has underlying map exactly
  `Scheme.relativeIterateFrobenius hp h r G.hom`, a pullback lift of the absolute
  Frobenius on `G` and `G.hom`. It is a `k`-morphism by the existing second
  projection identity. This is Milne 2.26's canonical map, not an arbitrary map.
- The tensor formula is an explicit final universal clause, for every
  `c : Γ(G.left, ⊤)` and `a : k`. In the target coordinate ring,
  `pullback.fst.appTop.hom c` is `c ⊗ 1` and
  `pullback.snd.appTop.hom ((Scheme.ΓSpecIso _).inv.hom a)` is `1 ⊗ a`.
  Their product is the pure tensor `c ⊗ a`. Applying the canonical map's
  `appTop.hom` gives exactly
  `G.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom a) * c ^ (p ^ r)`.
  The explicit `ΓSpecIso` and structure map express the coefficient `a` in `C`.
  This states `c ⊗ a ↦ a c^q` without introducing a second tensor construction.
- The group homomorphism assertion is `IsMonHom` on the canonical over-morphism,
  the recorded `def-sc-group-scheme` interface for group homomorphisms.
- Finiteness is `IsFinite` on its `.left` scheme morphism.
- Faithful flatness is precisely `Flat ... ∧ Surjective ...`, as explicitly
  defined in the item. The node does not require a separate ring-map predicate.
- Local finite presentation is `LocallyOfFinitePresentation ...`.
- The final quasi-compact fppf covering assertion is rendered by the same flat,
  surjective and locally finitely presented assertions together with
  `QuasiCompact ...`. These properties are stated once each.
- There is no `IsCommMonObj`, reductive assumption, rank restriction, positive
  dimension assumption, or exclusion of characteristic two.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (through the public field imports).
- `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`; its docstring identifies
  splitting with the nonconstant-polynomial-root formulation. The dependency's
  `AlgebraicClosure` is a construction, whereas its same recorded match explicitly
  supplies `IsAlgClosed` for the algebraically closed condition used here.
- `CategoryTheory.GrpObj`, `Mathlib.CategoryTheory.Monoidal.Grp`, and
  `CategoryTheory.IsMonHom`, `Mathlib.CategoryTheory.Monoidal.Mon`, publicly
  imported through `Mathlib.AlgebraicGeometry.Group.Affine`.
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`; checked also
  `connectedSpace_iff_clopen` in `Topology.Connected.Clopen`.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`.
- `AlgebraicGeometry.Spec` and `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `TensorProduct`, `Mathlib.LinearAlgebra.TensorProduct.Defs`, is the tensor
  notion in the affine pullback identification. The delivered signature uses
  the existing scheme pullback and its projections, so no private copy of
  the tensor construction or instance is needed. Read also the tensor inclusions
  and `Algebra.TensorProduct.productMap_apply_tmul`.
- `AlgebraicGeometry.IsFinite`, `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `AlgebraicGeometry.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, with
  `Flat.iff_flat_stalkMap` for the dependency's stalkwise definition.
- `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- Canonical Frobenius construction: `Scheme.iterateFrobenius` from
  `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`, and
  `Scheme.relativeIterateFrobenius` / `_snd` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius`.
  `Scheme.isOfCharacteristic_Spec` from
  `WeilConjectures.AlgebraicGeometry.GeometricFiberFrobenius` supplies its
  characteristic argument from `CharP.cast_eq_zero`.
- Base-change group operations: `Over.pullback` and
  `Over.grpObjMkPullbackSnd` / `Functor.grpObjObj`,
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` / `Monoidal.Grp`.

The plain imports retain the stated proof plan: AffineFiniteTypeAlgebra,
RelativeFrobeniusFinite, FinitePresentationOfFiniteLocallyNoetherian,
Geometrically.Reduced, faithfully flat algebra, exact localization, flat
localization, FunctionField, and prime-spectrum Noetherian facts. The existing
Group.Affine public import provides the coordinate Hopf and Hopf-spectrum
interfaces. The reduced-target dominant-group-flatness proof dependency has no
Lean declaration, and consequently has no module to import at this stage.

Source reading: Milne's PDF, printed pp.46--49, 2.24--2.29, gives exactly the
coordinate formula, pullback, product compatibility, group homomorphism, and
faithful flatness for smooth connected groups. Stacks `varieties.tex`,
`lemma-relative-frobenius-finite` (0CCD) and
`remark-n-fold-relative-frobenius` (0CCG), supplies the finite iterated map and
identical pullback convention. No source-based correction was required.

Edge cases checked: the trivial group `Spec k` is allowed, and its relative
Frobenius is an isomorphism; `p = 2` satisfies the only prime condition; `r = 1`
is included; `r = 0` is excluded exactly as in the node. Positive dimensional
additive groups are included and need not have an isomorphism Frobenius.
Noncommutative groups are allowed. The empty scheme is excluded by the node's
connectedness, and by existence of the group identity over the nonempty base.
The one universe `u` covers all sizes by enlargement and matches the library's
scheme-over-field convention; no independent smaller test-algebra universe is
quantified. The canonical field characteristic witness is derived rather than
added as a hypothesis.

Searches (all 2026-10-24):

- `msearch.py leansearch`: "The iterated relative Frobenius of a smooth connected
  affine group scheme is finite flat and surjective" returned eight ring
  Frobenius facts (`LinearMap.iterateFrobenius`, `iterateFrobenius`, injectivity,
  iteration identities, etc.), no matching group-scheme theorem.
- `msearch.py leanfinder`: "The relative Frobenius of a smooth connected affine
  algebraic group over an algebraically closed field is finite faithfully flat"
  returned eight hits including `Algebra.Smooth.flat`, perfect-field smoothness,
  and `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`; none asserts the
  node. The latter confirms the faithful-flat terminology used here.
- `msearch.py loogle`: `"frobenius", "Flat"` returned zero hits.
- `msearch.py grep`: `relativeFrobenius|frobenius.*[Ff]lat|Frobenius.*[Ff]lat`
  in Mathlib/AlgebraicGeometry returned zero hits.
- Direct `rg` over Mathlib/AlgebraicGeometry, `lean/WeilConjectures`, and
  `lean/Sheaf` for relative Frobenius and flat Frobenius found the existing
  canonical construction and finiteness/universal-homeomorphism results, but
  no theorem with the node's hypotheses and all conclusions. The general
  relativeFrobenius definition uses compatible endomorphisms; the more specific
  relativeIterateFrobenius used here constructs those endomorphisms canonically.
- `rg` for the node id in `lean/WeilConjectures` returned no hits. Searches for
  both proposed declaration names in Mathlib, WeilConjectures, Sheaf, and
  `dag/lean_names_upstream.json` returned no collisions.

Validation: `scompile.py Q54 lem-sfb-smooth-connected-group-frobenius-flat` compiled
both the sandbox and intended library module cleanly (2.1 s / 3.5 s); no errors
or warnings. No `#check`, private declaration, local notation, local instance,
or auto-bound variable is present. All postponed proof content is the single
named theorem matching this node, with all seven proof steps in its docstring.

## Second reading by Q54

I reopened the node and the complete delivered file for a separate second pass;
no second agent was started, as required by the dispatcher's explicit brief.
The maintainer's independent review remains separate from this worker reading.

The field, algebraic closedness and positive prime characteristic binders match
the first sentence. The over-object, group structure, affine and connected
instances, and the smooth and finite-type structure morphism instances match
all assumptions on G. The target uses the second projection of exactly the
Frobenius pullback, so it has the required second-factor scalar structure.
The scoped image-group instance fixes its operations to those obtained from G.
The helper definition bundles the existing canonical relative map, and its
last theorem clause explicitly tests every pure tensor with the stated order
of multiplication `a * c^q`. `IsMonHom` asserts compatibility of this map with
the specified group laws. `IsFinite`, `Flat`, `Surjective`,
`LocallyOfFinitePresentation` and `QuasiCompact` account for all remaining
clauses, including the fppf consequence. No additional class restricts G to
commutative or reductive groups, and no numerical condition excludes the
trivial group or p = 2. The theorem is only `sorry`; the helper's data is the
upstream construction, not a choice from an existence theorem. No mismatch was
found in this second pass and no correction to the mathematical node was made.


## Returned delivery repair (H2)

The maintainer returned immutable head `1ab223565f4e` because the statement
used two notions whose owning nodes were absent from the statement-dependency
closure. Added exactly `def-weil-absolute-frobenius-scheme` and
`def-pc-fibre-product` to the item's `stmt_deps`, as explicitly requested.
The former records `AlgebraicGeometry.Scheme.iterateFrobenius` in
`WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`, used in the target type
and affine formula. The latter records `CategoryTheory.Limits.pullback`,
`pullback.fst` and `pullback.snd` in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, used in that
same target and formula. Both are already landed nodes with usable records.
Their statements and records were reopened for this repair.

Compared the retained delivered node with the current read-only main node:
only the delivery's `lean` record differed before this repair. Preserved all
current main fields and the entire delivered `lean` record; the only new node
delta is these two additions to `stmt_deps`. The Lean module, mathematical
statement, proof and proof_deps are unchanged. No statement_change is needed.
The delivery wrapper rebases the repaired packet onto the current server base.

Second reading of the repair: the two added ids now directly name the owners
of the absolute Frobenius and fibre-product projections appearing in the
accepted signature. This repairs H2 without altering any mathematical clause,
canonical construction or edge case approved by the independent reviewer.
