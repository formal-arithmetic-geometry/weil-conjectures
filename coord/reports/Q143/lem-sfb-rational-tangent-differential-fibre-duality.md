## Worker report

The module `Sheaf.AlgebraicGeometry.RationalTangentDifferentialFibreDuality` states
`AlgebraicGeometry.exists_rationalTangent_differentialFibre_linearEquiv` with `sorry`.
The two helper definitions contain actual data: the composite structural residue ring map,
and global sections of the existing tensor pullback of the existing differential sheaf.
These package the map and object in this node; they introduce no independent notion.
The node copy changes only `lean`. No statement correction, new node, or dependency repair
is needed. There is one postponed theorem, matching the assigned DAG node, and its docstring
contains all four steps of that node's natural-language proof.

Hypotheses and clauses, in the order of the node:

- A field K: `(K : Type u) [Field K]`, with arbitrary explicit universe `u`.
- A scheme over K: `(X : Scheme.{u}) (f : X ⟶ Spec (.of K))`.
- A K-rational point: `(x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _)`.
  Composition is in diagrammatic order, so this is exactly f composed with x equals identity.
- Its underlying point x₀: `x (IsLocalRing.closedPoint K)`. A field spectrum has one point.
- Identify κ(x₀) with K by the structural map: `rationalTangentStructuralResidueMap K X f x₀`
  is exactly `(StructureSheaf.toStalk K (f x₀) ≫ f.stalkMap x₀ ≫ X.residue x₀).hom`.
  Rationality makes it an isomorphism. `Module.compHom` restricts the recorded tangent
  space's residue-field scalars along this particular map, without choosing another action.
- Mₓ = Γ(Spec K, x* Ω¹): `rationalTangentDifferentialFibre K X f x` is
  `(moduleSpecΓFunctor (R := CommRingCat.of K)).obj
  ((Scheme.Modules.tensorPullback x).obj f.relativeDifferentials)`.
  The global-section functor transports scalars by `Scheme.ΓSpecIso`, so these are
  K-vector-space global sections of the ordinary module pullback, exactly as specified.
- The tangent space is the recorded `schemeTangentSpace K X f x₀`, with the scalar
  restriction above. This retains the actual dual-number morphisms and their operations.
- The isomorphism with Hom_K(Mₓ,K): `∃ e : schemeTangentSpace ... ≃ₗ[K]
  (rationalTangentDifferentialFibre K X f x →ₗ[K] K)`.
- Canonical: the first conjunct fixes the value on every differential germ. For any
  local function a on U containing x₀ and any global section m whose germ is the germ
  of `tensorPullbackSection x f.relativeDifferentials U (d a)`, it requires
  `r (e θ m) = TrivSqZeroExt.snd (θ♯(aₓ₀))`. The proof `hθ` identifies the image of
  the dual-number closed point with x₀, giving the correctly typed stalk homomorphism
  `eqToHom ... ≫ Scheme.stalkClosedPointTo θ.val`. This is precisely the coefficient
  pairing of Stacks 0B2D. The condition on m imposes no extra hypothesis: a sheaf on
  the one-point space Spec K has its global sections equal to its stalk, so every such
  germ has a unique m. Differential germs span the fibre; hence the formula uniquely
  specifies the isomorphism and does not allow an arbitrary vector-space equivalence.
- The constant tangent vector: the last conjunct explicitly exhibits `θ₀` with
  `θ₀.val = Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r)) ≫
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K)) ≫ x` and `e θ₀ = 0`.
  The second and third maps are exactly x composed with p. The first transports
  dual-number coefficients by K → κ(x₀), as required for the recorded tangent space.
- No finite-type, smoothness, finite-dimensionality, Noetherian, characteristic, or
  algebraic-closure assumption occurs. Nothing is inferred from a chosen basis.

Dependency declarations read and used:

- `Field`, from `Mathlib.Algebra.Field.Defs` (the mathlib match of def-weil-field).
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, and `Spec.map`, from
  `Mathlib.AlgebraicGeometry.Scheme` (scheme and affine-spectrum dependencies).
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and
  `relativeDifferentialsDerivation`, from
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, supplied by the public upstream
  import of `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, and that module's
  `tensorPullbackSection`. This uses the dependency's recorded section normalization.
- `AlgebraicGeometry.schemeTangentSpace`, `schemeTangentSpaceAddCommGroup`, and
  `schemeTangentSpaceModule`, from `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`.
- `DualNumber` and its square-zero-extension operations, from `Mathlib.Algebra.DualNumber`.
  No alternate dual-number ring or alternate tangent space is introduced.
- `moduleSpecΓFunctor`, from `Mathlib.AlgebraicGeometry.Modules.Tilde`, is the existing
  K-module-valued global-section functor, publicly available through the differential module.
- `Scheme.stalkClosedPointTo`, from `Mathlib.AlgebraicGeometry.Stalk`, supplies the
  local-ring homomorphism used to read the epsilon coefficient.

The already stated proof dependencies are imported without `public`:
`WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
(`Scheme.Modules.exists_tensorPullback_stalk_iso`),
`Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion`
(`Scheme.Hom.conormalStalkFibre_shortExact_of_smooth`), and
`WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification`
(`exists_rationalPoint_tangent_cotangent_linearEquiv`). The conormal module supplies
closed-immersion and smoothness definitions; Stalk supplies the local-spectrum
correspondence, and the differential module supplies ring differentials. The proof-only
node `lem-sfb-relative-differentials-stalk` has no Lean record in the read snapshot, so
there is no recorded module to import for it yet. Its result is not needed to type this
statement, and its proof dependency and the full proof plan are retained unchanged.

Source checked: `literature/stacks-project/varieties.tex`, labels
`lemma-tangent-space-cotangent-space` and `lemma-tangent-space-rational-point`, including
the coefficient derivation and the cotangent-fibre paragraph immediately preceding 0B2D.
These impose no finite-type or smoothness assumption. No source issue or disputed
statement was found.

Edge cases checked mathematically before writing:

- X = Spec K and x = identity: differentials, tangent space, and the target dual vanish;
  the coefficient formula and zero-vector clause agree.
- The affine line at zero: da for its coordinate pairs with the epsilon coefficient,
  giving the usual one-dimensional isomorphism with the expected normalization.
- Spec K[t]/(t²) at zero, including characteristic 2: the fibre and tangent are both
  one-dimensional; no smoothness or characteristic exclusion has entered.
- Infinitely many polynomial variables at the zero point: the differential fibre is
  a direct sum and its full algebraic dual is a product. `→ₗ[K] K` is the full dual;
  neither a finite-support dual nor finite-dimensionality is substituted.
- Nonaffine X: normalization uses all open neighbourhoods U and their differential
  germs, rather than only global functions on X. Thus it still characterizes e.
- Empty X has no x from the nonempty field spectrum, exactly as in the node. The
  zero differential fibre is included. The scalar restriction uses the structural
  residue map, preserving rational points whose residue field is only isomorphic to K.

Searches made using the prescribed `msearch.py` wrapper:

- leanfinder: "The tangent space at a rational point of a scheme is canonically the
  linear dual of the fibre of the sheaf of Kahler differentials". Eight hits, including
  `Algebra.Extension.cotangentComplex_mk`, `Algebra.Extension.toKaehler`,
  `KaehlerDifferential.endEquivDerivation'`, and extension cotangent constructions.
  No scheme differential-fibre duality statement matched.
- loogle: `"TangentSpace", "KaehlerDifferential"`. Zero hits.
- grep: `tangent.*[Kk]aehler|[Kk]aehler.*tangent|relativeDifferentials`, restricted to
  Mathlib/AlgebraicGeometry. Zero hits.
- leansearch: "The tangent space at a rational point of a scheme over a field is the
  linear dual of the fibre of relative Kahler differentials". Eight hits: manifold
  `TangentSpace`, `KaehlerDifferential.D_apply`, extension exactness and cotangent space,
  `KaehlerDifferential.endEquivDerivation'`, `tensorKaehlerEquivBase`,
  `IsLocalRing.CotangentSpace`, and `fromIdeal`. None gives the scheme-level statement.
- `rg` in both project roots for rational tangents, tangent/differential combinations,
  and differential fibres found the existing tangent/cotangent and group-identity
  comparisons, which were read. They identify a cotangent quotient or require group
  structure; none states this arbitrary-scheme pullback differential-fibre result.
- Search for the exact node id in `lean/WeilConjectures` returned no occurrence.
  Search for all three proposed declaration names in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` returned no collision.

Validation: the complete delivered module compiled through `scompile.py`, both as the
sandbox module and under its intended library module name, with no errors or warnings.
All universe variables and term parameters are explicitly bound; auto implicits are
turned off. No other compile command or global build was run.


## Second reading by Q143

The delivered section said that no second worker was started (direct-delivery dispatcher
policy) and gave only a self-check. The maintainer's independent reviewer wrote this reading on
2026-10-24. It replaces that section and leaves the Worker report unchanged. The delivered Lean
file and the node record are not changed.

Node clauses and the Lean that renders each one
(`AlgebraicGeometry.exists_rationalTangent_differentialFibre_linearEquiv`):

1. Field K: `(K : Type u) [Field K]`. OK.
2. Scheme over K: `(X : Scheme.{u}) (f : X ⟶ Spec (.of K))`. The universe is the one of
   `schemeTangentSpace` (def-sc-scheme-tangent-space). OK.
3. K-rational point with f ∘ x = id: `(x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _)`
   (diagrammatic order). OK.
4. x₀ and κ(x₀) ≅ K by the structural map: `x (IsLocalRing.closedPoint K)` and
   `rationalTangentStructuralResidueMap` = `toStalk ≫ f.stalkMap ≫ X.residue`. This is the
   same composite that the landed `rational_tangent_cotangent_duality` and
   `ProductTangentSpaceDirectSum` use. Scalars are restricted along it by `Module.compHom`,
   so the residue-field module structure of def-sc-scheme-tangent-space is not replaced. OK.
5. M_x = Γ(Spec K, x^*Ω¹_{X/K}): `moduleSpecΓFunctor.obj ((tensorPullback x).obj
   f.relativeDifferentials)`. This uses the recorded ordinary tensor pullback
   (def-pc-module-pullback) and the recorded relative differential sheaf. It is a K-module
   through Mathlib's Γ functor on Spec K. OK.
6. Canonical K-linear iso T ≅ Hom_K(M_x, K): `∃ e : T ≃ₗ[K] (M_x →ₗ[K] K)` together with
   the pairing clause. For every θ, every U ∋ x₀, every a ∈ Γ(X,U) and every m whose germ
   equals the germ of `tensorPullbackSection x Ω U (d a)` (the actual section 1 ⊗ da), the
   clause requires r(e θ m) = ε-coefficient of θ♯(a_{x₀}). This is the coefficient pairing
   da ↦ D_θ(a) of Stacks 0B2D/0B2E. The space Spec K has one point, so each such germ comes
   from a unique m. The elements 1 ⊗ da span M_x ≅ Ω_{X,x₀} ⊗ κ over K, because r is
   bijective. So e is pinned and is not an arbitrary equivalence. The scalar convention is
   consistent: t·θ precomposes with ε ↦ tε, which multiplies D by t. `∃ hθ` is only the
   proof that θ sends the closed point to x₀, and that follows from the subtype condition. OK.
7. The constant vector x ∘ p goes to zero: `∃ θ₀, θ₀.val = Spec(mapRingHom r) ≫ Spec(inl) ≫ x
   ∧ e θ₀ = 0`. The first factor is needed because the recorded tangent space uses κ(x₀)[ε].
   θ₀ satisfies the subtype conditions, since r ∘ (residue map of x) = id by hx. So the clause
   is not vacuous, and it identifies θ₀ uniquely. OK.
8. No finite-type or smoothness hypothesis: none occurs. OK.

Edge cases: X = Spec K (both sides are zero); non-affine X (local U, not only global
functions); M_x = 0 (the zero clause still holds); infinite-dimensional fibre (`→ₗ[K] K` is the
full algebraic dual, as the node says); characteristic 2 (no restriction).

One definition per notion: Mathlib has no scheme tangent/differential-fibre duality.
`lem-sc-rational-point-tangent-derivation-identification` and
`lem-sc-rational-tangent-cotangent-duality` concern m/m², not x^*Ω, so they are not
duplicates. The two helpers are a composite of Mathlib maps and the Γ of the recorded pullback.
They have real data, docstrings and the blueprint tag. The node record differs from live only
in `lean`, and `lean.statement` is verbatim in the file. The proof is `sorry`, and the docstring
carries all four proof steps. No mismatch was found.
