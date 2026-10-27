## Worker report

The new module `Sheaf.AlgebraicGeometry.NoetherianNormalSteinModel` states
`AlgebraicGeometry.exists_noetherian_normal_stein_model`. Its sole theorem has
proof `sorry`; there are no new definitions or additional axioms. The node is
unchanged except for `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`, theorem
`theorem-stein-factorization-Noetherian` (Tag 03H0), its five clauses and proof;
`literature/stacks-project/morphisms.tex`, `lemma-normal-normalization` (Tag
035L), hypotheses, conclusion and proof. The latter applies to integral normal
source; an open subset of an irreducible space has at most one irreducible
component. No field, excellence, characteristic or normality of the base is
assumed here.

Hypothesis and conclusion correspondence:

- The integral schemes `T,B` are `{T B : Scheme.{u}} [IsIntegral T]
  [IsIntegral B]`. Integrality includes nonemptiness.
- Both schemes are Noetherian: `[IsNoetherian T] [IsNoetherian B]`.
  Mathlib's class is locally Noetherian plus compact. The theorem
  `isNoetherian_iff_of_finite_affine_openCover` in
  `Mathlib.AlgebraicGeometry.Noetherian` identifies it with exactly the node's
  finite affine cover by Noetherian section rings. This does not substitute
  mere local Noetherianness.
- The named morphism is `(f : T ⟶ B)`, proper by `[IsProper f]` and dominant
  by `[IsDominant f]`. The latter means its image is dense.
- Source normality is precisely `hT : ∀ x : T,
  IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x)`.
  Both clauses are present; no normality hypothesis on `B` appears.
- The intermediate scheme and morphisms are existential witnesses
  `(S : Scheme.{u}) (g : T ⟶ S) (q : S ⟶ B)`.
- Integrality of `S`, dominance of each map, and factorization are
  `IsIntegral S ∧ IsDominant g ∧ IsDominant q ∧ g ≫ q = f`.
  Lean composes from left to right.
- Normality of every local ring of `S` is the displayed universal conjunction
  of `IsDomain` and `IsIntegrallyClosed` on `S.presheaf.stalk x`.
- The second map is finite: `IsFinite q`. This includes affineness and
  finiteness of its section map on every affine base open.
- The first map is proper with geometrically connected fibres:
  `IsProper g ∧ GeometricallyConnected g`. The geometric predicate quantifies
  over field-valued base changes, including extension fields of residue fields.
- Every affine open `V = Spec A` is quantified as
  `∀ V : B.Opens, IsAffineOpen V → ...`, with `A = Γ(B,V)` and
  `R_V = Γ(T,f ⁻¹ᵁ V)`.
- The finite `A`-module clause is `(f.app V).hom.Finite`. This uses precisely
  `f`'s pullback on sections for the scalar action, without a new algebra
  structure or arbitrary identification.
- The canonical charts and maps are specified by
  `IsIso (g.app (q ⁻¹ᵁ V))` together with the preceding factorization and
  affineness of `q`. Here `g.app (q ⁻¹ᵁ V)` is the canonical section pullback
  `Γ(S,q⁻¹V) → Γ(T,g⁻¹(q⁻¹V))`. The equality `g ≫ q = f` identifies its
  target with `R_V`. Thus it supplies the canonical ring identification
  `Γ(S,q⁻¹V) ≅ R_V`, not merely an unspecified ring isomorphism. Since
  `q⁻¹V` is affine, its canonical affine-spectrum identification gives exactly
  `q⁻¹V ≅ Spec R_V`. Functoriality of pullback on sections and `g ≫ q = f`
  identify the second map with `Spec(f.app V)`. Under this same identification,
  the pullback of the first map is the identity of `R_V`, so the
  Spec/global-sections adjunction makes it evaluation. These local data are
  exactly the node's specification of the relative spectrum
  `Spec_B(f_* O_T)`. No separate relative-spectrum object or arbitrary
  factorization has been substituted. This encoding is also used in the
  related landed `exists_normal_stein_constant_field` theorem.

Dependency declarations and modules read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, from
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (including the equivalence of
  local finite type plus universal closedness with finite type here).
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, its affine-cover
  equivalences, and `AlgebraicGeometry.IsNoetherian` from the same recorded
  module `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, from
  `Mathlib.RingTheory.Noetherian.Defs`, used through the Noetherian scheme API.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`, the latter
  from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`; used directly on
  each local ring, in the recorded normal-domain form.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-pc-geometrically-irreducible`: the recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` module, supplemented by
  `Mathlib.AlgebraicGeometry.Geometrically.Connected` for exactly the connected
  clause of this multi-notion dependency, as its existing lean.note prescribes.
  The declaration used is `AlgebraicGeometry.GeometricallyConnected`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, from
  `Mathlib.AlgebraicGeometry.Scheme`; the affine chart characterization uses
  these existing notions.

The modules of all recorded proof dependencies are imported privately,
including relative normalization and its normal-stalk theorem, coherent
finite-type equivalence, coherent proper pushforward, affine section finiteness,
affine Stein factorization, affine adjunction, proper permanence and universal
closedness locality. Mathlib's `Normalization` supplies the relative
normalization node directly. No dependency interface repair was needed.

Edge cases checked before writing:

- Empty `T` and `B` are excluded by exactly the stated integrality hypotheses.
- The empty affine open is retained in the universal chart clause. Its section
  rings are zero rings; its finite ring map and the section isomorphism are
  meaningful. No nonempty-open restriction or domain assumption on `R_V` was
  introduced, so this case is retained.
- A proper dominant map is surjective; the nonempty geometric fibres in
  `GeometricallyConnected` are therefore compatible with the statement.
- Neither separability nor algebraic closedness of residue fields is assumed.
- Identity maps and finite dominant maps from normal integral schemes are
  included. The first Stein map in the finite case is an isomorphism.
- Non-normal integral bases are included. No field of definition or finite
  type over a field is required.
- The explicit common scheme universe is `u`; all variables and universes
  are bound and `autoImplicit` is false.

Searches (all via the prescribed `msearch.py`, recorded in `searches.jsonl`):

- LeanFinder: "Proper dominant morphism of integral Noetherian schemes with
  normal source has a finite normal Stein factorization with geometrically
  connected fibres". Eight hits, all relative-normalization ingredients;
  none states the finite normal Stein model theorem.
- Loogle: `AlgebraicGeometry.GeometricallyConnected,
  AlgebraicGeometry.IsProper`. Zero hits.
- LeanSearch: "Stein factorization proper morphism normal Noetherian schemes
  finite geometrically connected". Eight hits on properness, finiteness and
  normalization; none states this theorem.
- Mathlib grep: `steinFactorization|normal_stein|Stein`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Stein-related names:
  found `WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine` (only an
  affine base) and `Sheaf.AlgebraicGeometry.NormalSteinConstantField` (requires
  finite type over a field, also states constant-field properties). Their full
  statements and docstrings were read. Neither states this general Noetherian
  theorem, so no existing binding is exact.
- Direct grep of the item id in `lean/WeilConjectures`: no match. Direct grep
  for `exists_normal_stein_model|noetherian_normal_stein` across Mathlib,
  `WeilConjectures` and `Sheaf`: no name collision.

Compilation: `scompile.py Q96 lem-sfb-noetherian-normal-stein-model` compiled
both sandbox and library module modes cleanly, in about two seconds each.
No statement dispute or node fault was found.

## Second reading by Q96

Author's separate second pass, not an independent-agent review: reopened the
node, source passages and final module and checked the correspondence above.
The maintainer supplies the independent review required by this dispatch.
Both Noetherian hypotheses, both integral schemes, properness, dominance and
the two stalk-normality conjuncts are present. Each existential map has the
correct direction and the composition equation has the correct order. The
universal chart clause retains all affine opens, including the empty one,
and its finite ring map uses the canonical pullback. Checked especially that
an arbitrary factorization would not satisfy the section-isomorphism clause:
this clause is precisely what supplies the relative-spectrum identification
and the identity-on-sections evaluation condition. No extra field or normal
base assumption was introduced. Corrected one proof-plan wording to distinguish
the integral intermediate scheme from the merely dominant first morphism.
No mathematical mismatch or node correction was needed.
