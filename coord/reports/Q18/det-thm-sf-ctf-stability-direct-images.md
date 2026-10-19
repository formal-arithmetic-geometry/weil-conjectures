## Worker report

The module `lean/Sheaf/SixFunctors/CtfStabilityDirectImages.lean` states
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_stability_direct_images`.
It introduces no new data definitions. The coefficient hypothesis is
`IsLocalizingAdmissibleCoefficient ℓ Λ`, with `MonObj` and `IsCommMonObj` instances. The
standing schemes are `X,Y : Scheme.{u}` over `Spec k`, separated, quasi-compact and locally
of finite type; `f` is over `Spec k`, locally of finite type, quasi-compact and separated.
The explicit `HasCompactification.of_isOver` term supplies the canonical compactification
used by the recorded derived lower-shriek functor without adding a compactification
hypothesis.

For every occurrence of `Dctf(T,Λ)`, the Lean statement renders membership as
`constantModelBoundedConstructible Λ T K ∧ DerivedCategory.finiteTorAmplitude _ K`, exactly
bounded constructibility plus finite Tor amplitude from `sk-def-sfb-constructible`. The four
parts of the source statement are rendered as follows.

1. The first conjunct quantifies an object `K` of the derived category of module objects on
   `Y`; its Dctf hypothesis implies both
   `constantModelBoundedConstructible Λ X ((L((f)^*⟦Λ⟧)).obj K)` and the corresponding finite
   Tor-amplitude predicate. This is the derived pullback clause.

2. The second conjunct quantifies two Dctf objects `K,M` on `X` and applies the relative
   derived tensor `((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M`, preserving both predicates.

3. The third conjunct quantifies standing schemes `S,Sbar`, a factorization
   `a = u ≫ i`, and the over-base, open-immersion and closed-immersion instances. It sends a
   Dctf object on `S` to the termwise derived locally closed extension
   `(D((u)_!open⟦Λ⟧) ⋙ R((i)_*⟦Λ⟧)).obj K` on `X`, preserving both predicates. This is the
   `a_!` clause; the factorization is explicit so the source's locally closed immersion is
   represented by the canonical open-then-closed construction.

4. The fourth and fifth conjuncts preserve Dctf under `R((f)_*⟦Λ⟧)` and under
   `rightDerivedLowerShriekOfCompactification Λ c_f`, respectively. The final conjunct
   quantifies any localizing-closure restriction and any right adjoint `G` of that restricted
   lower-shriek. It says every Dctf object `K` on `Y` is sent by `G` to a Dctf object on `X`;
   the subtype term `⟨K, fun P _hP hS ↦ hS K hK⟩` is the canonical inclusion of a Dctf object
   into its localizing closure. The previous `sk-prop-sf-existence` statement supplies the
   required closure data and right adjoint, while universal quantification makes the chosen
   right adjoint independent of its unique-isomorphism choice.

Dependency declarations used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients` —
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; the imported
  `Sheaf.Paper.LocalizingClosure` supplies `localizingClosureProEtale`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` —
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`,
  `AlgebraicGeometry.HasCompactification.of_isOver`, and the published bounded-constructible
  module-object interfaces.
- `Sheaf.Paper.CondensedConstantConstructibility` —
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and its finite-constant
  constructibility declarations.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` —
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` and the
  `L((f)^*⟦Λ⟧)` / `R((f)_*⟦Λ⟧)` functors.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` — the recorded
  `derivedHom`/derived-tensor closed structure, including the relative derived tensor used in
  clause 2.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek` —
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.Paper.LocalizingExceptionalAdjoint` —
  `AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek` and
  `exists_localizingExceptionalAdjoint`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` —
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` (imported by the
  lower-shriek modules) — `openImmersionLowerShriek` and `lowerShriek`.
- `Sheaf.SixFunctors.IntTensorProjection` —
  `AlgebraicGeometry.ProEtale.CondensedRing.locallyClosedImmersionTensorProjection`, the
  canonical locally closed projection interface used by the proof plan.

Edge cases checked before writing the signature: the universal object binders allow empty
schemes and zero objects; the two-object tensor clause allows either input to be zero; the
locally closed clause allows identity open or closed factors and the empty locally closed
subscheme; no nonemptiness or finite-index assumption is imposed; arbitrary coefficient
stages include finite rings (including the zero ring), the two integral/rational stages and
finite subextensions/algebraic closure; and `p ≠ ℓ` is retained through
`Fact (ringChar k ≠ ℓ)`. The localizing-closure subtype works for the empty coproduct as well
as arbitrary set-indexed coproducts.

Searches made:

- `msearch.py ... leanfinder "pullback tensor product locally closed extension by zero direct images exceptional pullback preserve bounded constructible finite Tor objects"`:
  eight unrelated Mathlib hits (light-condensed internal projectivity and module pullback), no
  exact theorem.
- `msearch.py ... loogle "DerivedCategory finiteTorAmplitude constantModelBoundedConstructible rightDerivedLowerShriek leftDerivedUpperStar"`:
  no hits (`finiteTorAmplitude` was unknown to Loogle).
- `msearch.py ... grep "constructibleFiniteTor|constantModelBoundedConstructible|stability_direct_images" Mathlib/CategoryTheory`:
  no hits.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration with this node id
  or the final theorem name; it found only the underlying generic stability interfaces and
  existing constant-model lemmas. A direct `grep` for the node id also found no existing
  declaration.

The file was compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q18 det-thm-sf-ctf-stability-direct-images
<file>`; sandbox and library-side compilation both completed with no errors or warnings.

Final binder audit: every standing hypothesis is now an explicit theorem binder, including
coefficient admissibility and the characteristic facts; no section-variable omission is
possible. The full ten-step natural-language proof is in the theorem docstring.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
