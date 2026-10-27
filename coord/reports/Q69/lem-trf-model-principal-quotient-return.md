## Worker report

The module `Sheaf.AlgebraicGeometry.ModelPrincipalQuotientReturn` states
`AlgebraicGeometry.modelPrincipalQuotientReturn`, with one postponed proof and no new
definitions. The node statement, dependencies and proof remain unchanged. Its source is
Stacks Project, Tag 056Y, `lemma-slice-given-element`, proof paragraph 2: return from the
cartesian model and tensoring the flat principal quotient with the original base ring.
The current latest blueprint ancestor `lem-trf-local-term-locality` and its proof were
also read; this delivery formalizes the separately split algebraic return step.

Hypotheses, in node order:

- The schemes and morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The affine opens are `U₁ : X.Opens`, `V : S.Opens`, with `hU₁ : IsAffineOpen U₁`
  and `hV : IsAffineOpen V`. Their rings `B` and `A` are the actual section rings
  `Γ(X, U₁)` and `Γ(S, V)`. This uses the canonical affine charts rather than
  introducing arbitrary coordinate-ring isomorphisms.
- The containment `f(U₁) ⊆ V` is `hUV : U₁ ≤ f ⁻¹ᵁ V`. The algebra structure is
  identified with the induced ring map by `hcompat : algebraMap Γ(S, V) Γ(X, U₁) =
  (f.appLE V U₁ hUV).hom`. This is the meaning of the node's algebra structure on
  its affine chart, not an extra geometric assumption.
- Finite presentation of `B` over `A` is
  `[Algebra.FinitePresentation Γ(S, V) Γ(X, U₁)]`.
- The rings `A₀`, `B₀` have their explicit `CommRing` instances; the ring map
  `A₀ → A` and the `A₀`-algebra structure on `B₀` are `[Algebra A₀ Γ(S, V)]` and
  `[Algebra A₀ B₀]`. The model isomorphism is
  `e : Γ(S, V) ⊗[A₀] B₀ ≃ₐ[Γ(S, V)] Γ(X, U₁)`.
- The point is `x : U₁`; its prime `q` is exactly `hU₁.primeIdealOf x`. The
  elements `a₀ g₀ : B₀` and `a g : Γ(X, U₁)` have defining equations
  `ha : a = e (1 ⊗ₜ[A₀] a₀)` and `hg : g = e (1 ⊗ₜ[A₀] g₀)`.
  These equality binders name the two elements defined in the node, without hidden lets.
- Membership and nonmembership are `haq : a ∈ (hU₁.primeIdealOf x).asIdeal` and
  `hgq : g ∉ (hU₁.primeIdealOf x).asIdeal`.
- Flatness of `H₀` is `[Module.Flat A₀ (Localization.Away g₀ ⧸
  Ideal.span {algebraMap B₀ (Localization.Away g₀) a₀})]`.

Conclusions, clause by clause:

- `IsAffineOpen (X.basicOpen g)` and the existential proof `hxg : x.1 ∈ X.basicOpen g`
  assert that `U = D(g)` is an affine open neighbourhood in the original `X`.
- The displayed equality of `X.presheaf.germ` values applies restriction
  `X.presheaf.map (homOfLE (X.basicOpen_le g)).op` to `a`, and identifies its germ
  with `X.presheaf.germ U₁ x.1 x.2 a`. Both sides lie in the same stalk of `X`.
- The isomorphism `i : Spec (CommRingCat.of (Localization.Away g)) ≅
  (X.basicOpen g).toScheme` identifies this exact basic open with `Spec B_g`.
  Its equation `i.hom ≫ (X.basicOpen g).ι = Spec.map (CommRingCat.ofHom
  (algebraMap Γ(X, U₁) (Localization.Away g))) ≫ hU₁.fromSpec` fixes the chart
  identification over `X`; it is not an unconstrained choice of morphism.
- `D` is literally the spectrum of `Localization.Away g ⧸
  Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}`.
  `IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ i.hom)`
  is the asserted closed immersion into `U`. The existential point `y : D` and
  its displayed image equation say this closed subscheme contains `x` in `X`.
- `Flat` and `LocallyOfFinitePresentation` apply to the actual composite
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ i.hom ≫
  (X.basicOpen g).ι ≫ f`, so the given morphism to the original base is retained.
- The existential `E` is an `A`-algebra equivalence from `A ⊗[A₀] H₀` to that
  literal quotient `B_g/(a)`. Its formula is universally quantified over
  `c : Γ(S, V)`, `b₀ : B₀`, `n : ℕ`. Fractions `b₀/g₀^n` are rendered by
  `algebraMap B₀ (Localization.Away g₀) b₀ * IsLocalization.Away.invSelf g₀ ^ n`;
  the right hand side is the class of
  `algebraMap _ _ (algebraMap Γ(S, V) Γ(X, U₁) c * e (1 ⊗ₜ[A₀] b₀)) *
  IsLocalization.Away.invSelf g ^ n`. Thus the prescribed map on all fractions,
  including exponent zero, is present.
- The final `Module.Flat Γ(S, V) (...)` and `Algebra.FinitePresentation Γ(S, V) (...)`
  are flatness and finite presentation of the same quotient over `A`.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; affine opens, section rings and `IsAffineOpen.fromSpec` come
  from `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation`.
- `def-weil-pbc-module-tensor-product`: the Mathlib match `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with `TensorProduct.tmul`; its
  commutative algebra structure is supplied by `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-flat-ring-map`: `Module.Flat` in `Mathlib.RingTheory.Flat.Basic`,
  the module-flatness declaration recorded with `RingHom.Flat` in
  `Mathlib.RingTheory.RingHom.Flat`.
- `def-weil-ring-localization-away`: `Localization.Away` from
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with its ring structure and
  `IsLocalization.Away.invSelf` from `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.

The proof plan is transcribed step by step in the theorem docstring. The recorded
Mathlib matches for the proof nodes were read, including `SpecMap_appLE_fromSpec`,
`IsLocalization.Away.tensorProductEquivTMulRight`, tensor quotient base change,
`Module.Flat.baseChange`, the polynomial quotient presentation,
`Algebra.FinitePresentation.quotient`, localization flatness and composition.
The corresponding available proof modules are imported with plain `import`.
There are no project prerequisites requiring a new node or dependency repair.

Edge cases checked mathematically before writing:

- `a₀ = 0` gives the zero defining ideal and the whole localized chart as `D`.
- A unit `g₀` gives an unchanged affine chart; exponent `n = 0` in the formula is
  explicitly included. Taking `g = 1` therefore recovers the original affine open.
- If `g₀` is nilpotent, its image `g` is nilpotent, contradicting `hgq` at every
  prime, so this impossible input is excluded by the stated hypotheses themselves.
- A unit `a` cannot satisfy `haq`. The actual point assertion ensures `D` is
  nonempty in the allowed cases; no artificial `Nonempty` assumption is added.
- Empty `U₁` and the zero ring `B` admit no such `x : U₁`, as in the node.
  An empty `S` is also incompatible with this point and the given morphism.
- No flatness of `A₀ → A`, and no flatness or finite-presentation hypothesis on
  `f` away from these charts, is assumed.
- `u`, `v`, `w` are explicitly bound and independent: the two model rings may
  have different universes from the schemes. No equality of these universes is imposed.

Searches made for an existing complete statement:

- `msearch.py`, leanfinder, query “A flat model principal quotient returns to an
  affine chart with quotient base change isomorphism and flat locally finitely
  presented composite”: 8 hits, headed by `AlgebraicGeometry.Flat.flat_appLE`,
  `Scheme.Hom.flat_appLE`, and `Flat.flat_of_affine_subset`. These give component
  flatness criteria, not this statement or its fraction formula.
- `msearch.py`, loogle, query `"Flat", "IsLocalization", "Quotient"`: 0 hits.
- `msearch.py`, grep, query `quotient.*tensor|tensor.*quotient|localization.*quotient`
  in `RingTheory/TensorProduct`: 5 hits in `TensorProduct/Quotient.lean`; these
  concern quotient tensor identities and do not state the whole chart return.
- `rg` of the project and upstream library for `principalQuotient`, `modelPrincipal`,
  `principal_quotient`, and the exact node id: only unrelated Koszul quotients,
  local algebra results, and other coefficient models. No complete match.
- The prescribed exact-node-id `grep -rn` of `WeilConjectures` returned no match.
- A name-clash search for `modelPrincipalQuotientReturn` in Mathlib, `WeilConjectures`
  and `Sheaf` returned no declaration.

No statement dispute or node fault was found. The theorem has exactly the required
`sorry` proof. There are no helper definitions or extra postponed assertions.

Validation: the delivered module compiled using `scompile.py`, both as the sandbox
module and under its final library name, with no errors or warnings. Delivery preflight
and its repeat compilation are run with `deliver2.py --no-push` before pushing.

## Second reading by Q69

No second worker was started: the dispatcher brief prohibits other agents and directs
this worker to deliver itself. The maintainer's independent review supplies the second
reading. A final self-check matched each hypothesis and conclusion above with the node:
the `i.hom` compatibility fixes the chart in `X`; the quotient map is canonical; the
fraction formula retains `c`, `b₀` and every `n`; the flat and locally finitely presented
map is explicitly the composite with `f`. No mismatch or statement correction was found.
