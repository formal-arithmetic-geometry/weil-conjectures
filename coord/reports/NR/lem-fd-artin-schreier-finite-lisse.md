## Worker report

`Sheaf/FourierTransform/ArtinSchreierFiniteLisse.lean` states
`AlgebraicGeometry.Scheme.isFlat_isConstructible_isLisse_artinSchreierSheafOfNatCastEqZero`.
The only postponed theorem is this item, with proof `sorry`. Its docstring follows
all ten current DAG proof steps, including the module-linear, translation-equivariant
finite-exchange comparison between the pullback definition and the relative projector image.
No mathematical statement or dependency list was changed.

Hypothesis-by-hypothesis correspondence:

* `{p : ℕ} [Fact p.Prime]` states that `p` is prime.
* `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [Invertible (p : Λ)]`
  states precisely that the commutative coefficient ring is finite and `p` is a unit.
* `{X : Scheme.{u}}` and `h : (p : Γ(X, ⊤)) = 0` state the characteristic condition
  without assuming that the scheme is nonempty or that its global ring is nonzero.
* `b : Γ(X, ⊤)` is the specified global function.
* `Ψ : AddChar (ZMod p) Λ` is an additive character with unit values: the character
  identities imply `Ψ a * Ψ (-a) = 1`. No primitivity or nontriviality is assumed.

Object and conclusion correspondence:

* `zmodRingHomOfNatCastEqZero h` is the canonical ring map from `F_p`, using `ZMod.lift`
  and integer casts. Its ring-hom fields are actual proofs, with no postponed data.
  `overSpecZModOfNatCastEqZero h` is the resulting scheme structure map, with the
  finite field lifted to the scheme universe. It works also for the zero global ring.
* `artinSchreierSheafOfNatCastEqZero h Ψ b` invokes the existing upstream
  `AlgebraicGeometry.Etale.artinSchreierSheafOf`, with this canonical structure map
  and the character transported along `AddEquiv.ulift`. The upstream definition is
  the inverse image along `b` of `image (artinSchreierIdempotent Ψ)`; that idempotent
  is exactly the weighted sum `p⁻¹ ∑ a, Ψ(-a) σ_a`. Thus this is the current
  general-coefficient construction of `def-fd-artin-schreier-sheaf`, not its older
  finite-type, Qbar-coefficient text. The relative-projector interpretation is proved
  by DAG steps 3–5, which are explicitly retained in the theorem's proof docstring.
* `artinSchreierCoverOfNatCastEqZero h b` is the actual pullback of the universal
  polynomial map `artinSchreierMap ... p` along the map defined by `b`.
  This is the relative spectrum of `O_X[T]/(T^p-T-b)`: on every affine open,
  its universal property is exactly a base map and a root of that equation.
  `artinSchreierCoverMapOfNatCastEqZero h b` is `pullback.snd`, the prescribed `q`.
* The first three conjuncts, `IsFinite q ∧ Etale q ∧ Surjective q`, give every
  asserted property of this covering.
* `Nonempty ((Etale.upperStar (ModuleCat ...) q).obj L ≅ 𝟙_ _)` is the required
  module-sheaf isomorphism `q⁻¹ L ≅ Λ_Y`: the monoidal unit is the constant free
  rank-one module sheaf. Along this explicit étale surjection it supplies precisely
  the rank-one local trivialization. The subsequent `IsLocallyConstantSheaf L`
  states lissity/local constancy in the recorded module-valued encoding. Finite
  coefficients and the displayed trivialization give finite local values.
* `IsConstructibleEtaleModuleSheaf L` is the recorded constructibility predicate,
  using finite locally closed strata with constructible parts and finite constant
  module values, rather than a different upstream stratification convention.
* `CategoryTheory.exactFunctor _ _ (tensorRight L)` states precisely exactness of
  `G ↦ G ⊗ L`, the definition of flatness in Stacks Tag 03ER(3). The current
  `def-pc-flat-sheaf-modules` record explicitly exposes this existing predicate for
  the `Sheaf (ModuleCat Λ)` encoding; the general `SheafOfModules.IsFlatOnSite`
  interface is preserved without any replacement or duplicate flatness definition.

Dependencies read and used:

* `WeilConjectures.FourierTransform.ArtinSchreier`:
  `AlgebraicGeometry.Etale.artinSchreierSheaf`, `artinSchreierIdempotent`, and
  `artinSchreierSheafOf` (the closed upstream declarations of the dependency's audit).
* `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and
  `WeilConjectures.ConstructibleSheaf.Defs`: `CategoryTheory.Sheaf`, the
  `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)` coefficient convention,
  `AlgebraicGeometry.Scheme.LocallyConstantDatum`, and `IsLocallyConstantSheaf`.
* `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` and its existing underlying
  `CategoryTheory.exactFunctor`, as the current dependency's note prescribes.
  The canonical sheaf monoidal structure is imported through the upstream
  `WeilConjectures.ConstructibleSheaf.Monoidal`.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, the canonical inverse image by left Kan
  extension and sheafification, supplied transitively by the Artin–Schreier module.
* The modules of the stated proof dependencies are imported without `public`;
  the two proof nodes without recorded Lean interfaces are not fabricated.

Edge cases checked: the empty scheme, zero global ring, zero coefficient ring,
trivial character, `p = 2`, and arbitrary `b` including zero. In particular,
`CharP Γ(X, ⊤) p` would wrongly exclude the empty scheme; the saved construction
correctly uses only `h`. No finite-type, field, local-ring, nonempty, or faithful
character hypothesis occurs. `ULift` changes only the finite field's universe and
its transported character, not the characteristic or covering.

Searches retained from the saved packet and checked against the current sources:

* `msearch.py NR lem-fd-artin-schreier-finite-lisse leanfinder` with query
  "finite commutative coefficient ring Artin Schreier sheaf characteristic p
  scheme locally free rank one": eight hits on Witt-vector isocrystals,
  Frobenius, and algebraic étale criteria, no matching sheaf theorem
  (saved machine log `searches.jsonl`, 2026-10-18).
* The node records LeanSearch query "Artin Schreier sheaf attached to a character
  is locally free rank one on the etale site": unrelated structure-sheaf/free-module
  hits; Loogle query `"ArtinSchreier"`: zero hits. Its further LeanFinder query on
  the image of a character averaging projector finds representation-averaging
  results, not this étale-sheaf theorem.
* Mathlib grep searches `ArtinSchreier`, `character.*sheaf`, and `locally.*free`
  find algebraic étale maps or generic locally free sheaves, not this statement.
* Project/source `rg` finds `artinSchreierSheafOf`, which is reused, and its
  `CharP` specialization, which excludes the zero-ring edge case. There is no
  existing theorem asserting all the relative-cover, trivialization,
  constructibility, and flatness clauses with these hypotheses.
* Resumption `rg` across Mathlib, upstream `WeilConjectures/`, and published
  `lean/Sheaf/` for all five helper names finds no collisions. Their data is
  retained from the saved attempt, consolidated into this item's module.

Source self-check: opened the current blueprint definition
`main-20261015/.../sk-def-as/def-fd-artin-schreier-sheaf.md`, Stacks
`etale-cohomology.tex` section `section-artin-schreier` (0A3J), and
`sites-modules.tex` definition `definition-flat` item (3) (03ER), as well as the
upstream construction and the exact dependency signatures/docstrings.
No STATEMENT-DISPUTED flag or statement correction is needed.

## Second reading by NR

The resumed worker reopened the saved node, module, report, and the current
recorded dependencies for the required self-check. Each binder and each clause
is matched above. The finite/étale/surjective cover and its displayed constant-line
trivialization are all present; `IsLocallyConstantSheaf` is read together with
that trivialization, so rank one is not silently replaced by arbitrary rank.
The relative polynomial cover is the canonical pullback, not an unspecified
étale cover, and the module defined by pullback is the actual upstream character
projector construction.

Two saved interface defects were repaired: the new narrow dependency bindings
would replace the general finite-field Artin–Schreier definition and the general
ringed-site flatness definition. Both dependency-node copies were removed from
this delivery. The canonical characteristic-condition helpers were retained in
the item's own module and listed in `lean.declarations`. The theorem now uses the
current dependency's existing `exactFunctor _ _ (tensorRight L)` interface;
no flatness helper or replacement dependency module remains. The theorem's
proof docstring now includes all ten DAG steps and the stated proof modules
are imported. The mathematical item statement and all its dependencies remain
unchanged. The first dry run's two line-width warnings were fixed.

Validation: `scompile.py NR lem-fd-artin-schreier-finite-lisse` compiled the
consolidated module both as sandbox and library, without errors or warnings,
including after the proof-dependency imports were added. Every variable and
universe is explicitly bound, with `set_option autoImplicit false`. Definitions
have real data; the only `sorry` is the named item theorem. The item node differs
from the repository only in `lean`, whose signature is copied verbatim.
