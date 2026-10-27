## Worker report

The module `Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection` states
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object`.
Its sole theorem has proof `sorry`; no definitions or other postponed results are introduced.
The node statement and dependencies are unchanged.

Hypotheses and clauses, individually:

- The field is `(k : Type u) [Field k]`.
- The Noetherian commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ]`. There is no finite-ring or torsion-ring hypothesis.
- The schemes are `{X Y : Scheme.{u}}` with `X.Over (Spec (.of k))` and
  `Y.Over (Spec (.of k))`, so their structure morphisms are the ones recorded by the node.
- Finite type of each structure morphism is its `LocallyOfFiniteType` and
  `QuasiCompact` instances. This does not impose separatedness of either structure map.
- `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` gives the k-morphism, and `[IsSeparated f]`
  gives exactly its separatedness. Properness is not assumed.
- `(E : DerivedCategoryModule Λ X)` is an object of the ordinary unbounded derived
  category of small-etale module sheaves. `_hbounded : ∃ c d : ℤ, E.IsGE c ∧ E.IsLE d`
  says it belongs to the bounded full subcategory, with unrestricted integer bounds.
- `(a b : ℤ) (_hab : a ≤ b)` renders the finite interval [u,v], renaming its endpoints
  to avoid confusion with Lean's universe name. `_hTor : DerivedCategory.hasTorAmplitudeIn
  Λ X a b E` is the recorded all-module-sheaf Tor-amplitude predicate.
- `(N : ℕ) (_hNpos : 1 ≤ N)` renders the positive integer. Since the integer is positive,
  natural scalar multiplication is the same action as its integer scalar multiplication.
  `_hN : N • 𝟙 E = 0` annihilates the identity of E, not merely its homology sheaves.
- `_hNY : IsUnit (N : Γ(Y, ⊤))` states invertibility on Y; a global section is a unit
  exactly when it is a unit in every stalk, including the empty scheme case.
- `(M : ModuleCat.{u + 1} Λ)` quantifies over every module in the project's coefficient
  universe, with no finite generation, presentation, flatness or projective-dimension data.
  There is no constructibility assumption on E.
- `constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)` is the recorded sheafification
  of the constant module presheaf, and `DerivedCategory.singleFunctor _ 0` puts it in degree 0.
- The conclusion is `IsIso` of the component of the exact recorded canonical counit mate
  `rightDerivedLowerStarProjectionMap` at E and this constant module in degree zero.
  Its source is `Rf_*E ⊗ᴸ M_Y[0]`; its target is `Rf_*(E ⊗ᴸ Lf* M_Y[0])`.
  The latter is canonically identified with `Rf_*(E ⊗ᴸ M_X[0])`. This is the identification
  explicitly specified in the node, not an arbitrary comparison or an existence of some iso.
  The source module's `rightDerivedLowerStarProjectionMap_app_app` and
  `homEquiv_symm_rightDerivedLowerStarProjectionMap` fix the arrow as the counit mate.
- Naturality in E and M is built into that existing natural transformation of bifunctors,
  restricted along `constantSheaf ⋙ singleFunctor`; it is not a separately chosen family
  of isomorphisms. Its inverse is consequently natural too. Constant inverse image is
  the natural `Scheme.upperStarConstantSheafIso`, followed by
  `singleFunctorCompLeftDerivedUpperStarIso`. Thus the IsIso assertion supplies the
  derived isomorphism and its naturality, rather than just cohomology-degree isomorphisms.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `Separated`: `IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, the recorded unbounded encoding, with the standard
  derived t-structure `IsGE`, `IsLE` describing the bounded subcategory.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  its total right derived functor is precisely the functor used by the projection map.
  The dependency also records `rightDerivedLowerStarPlus` for the bounded-below restriction;
  this statement uses the unbounded right derived functor already used in the projection-map
  dependency, as expressly required by the item's statement.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`, already
  used in both bifunctors of the canonical mate; no completed tensor is involved.
- `Mathlib.Algebra.Homology.Additive`: `Functor.mapHomologicalComplex` (the recorded
  termwise constant construction); its degree-zero specialization uses `constantSheaf`
  and `DerivedCategory.singleFunctor`, without redefining either.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap` and its two transpose equations.
  The standard module instances are supplied by
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` records the mixed dependency interface:
  the bounded predicate `Etale.DerivedCategory.hasTorAmplitudeIn` is already in the upstream
  `Coefficients` module. This delivery uses that predicate, not a new copy.

All proof dependencies that have recorded modules are imported without `public`, except
those already publicly imported for their statement use. The fixed-exponent coproduct node
`lem-sf-fixed-exponent-derived-coproducts` currently has no recorded Lean declaration or
Mathlib match; it is not a statement prerequisite and hence supplies no module to import.
The proof docstring retains its role explicitly. No dependency repair is needed to type this
item's statement. The five proof steps in the docstring follow the node, including the fixed
annihilator argument rather than assuming that E lifts to a complex of Λ/N-modules.

Edge cases checked before writing: E = 0 and M = 0 give zero-object arrows; N = 1 forces
E = 0; the zero coefficient ring is allowed; no nonzero module or ring is assumed. Empty X
and empty Y are not excluded by a Nonempty assumption. Negative and equal interval endpoints
are allowed, with exactly a ≤ b as in the node. Arbitrarily large modules are accommodated
by choosing the project universe large enough; the site and coefficient universe convention
is the recorded six-functor one. No finite cohomological dimension of the base field is added.
The theorem is the relative extension of 0F12 explicitly stated by the node, not the literal
absolute torsion-ring version. Stacks `etale-cohomology.tex` definitions and proofs around
`definition-cd-f`, `lemma-finite-cd`, `lemma-finite-cd-mod-n-direct-sums`, and
`lemma-pull-out-constant-mod-n` were read, as was the direct-image stability docstring.

Searches for an existing statement:

- `msearch.py leanfinder`: "Derived projection formula for etale pushforward of a bounded
  torsion complex with an arbitrary constant module"; eight unrelated algebraic-etaleness
  and Kaehler-differential hits; no match.
- `msearch.py leansearch`: "Projection formula for derived etale direct image with arbitrary
  constant module and bounded torsion object over a Noetherian ring"; eight algebraic-etale
  ring/algebra hits; no derived sheaf projection formula.
- `msearch.py loogle`: `"projectionFormula"`; zero hits.
- `msearch.py grep`: `projectionFormula|projection_formula|pull.out.constant` in
  Mathlib/CategoryTheory; zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for projection/constant, torsion/projection,
  and `isIso.*constant` found the canonical mate and comparison already used above, the finite
  coefficient/finite-module theorem in `DirectImageTorAmplitude`, the finitely presented
  constant theorem in `FiniteConstantProjectionFormula`, the countable-coproduct/finite-module
  theorem in `ConstantTensorProjection`, and proper torsion projection formulas. None has the
  current conclusion for an unrestricted M under precisely the current hypotheses.
- `grep -rn lem-sf-projection-torsion-object-constant lean/WeilConjectures`: no hits.

Validation: scompile.py compiled this single delivery file against the published live library
in 4.3 seconds (and its sandbox check in 4.7 seconds), with no compiler errors or warnings.
`autoImplicit false` ensures all variables and universes are bound explicitly. No statement
fault or STATEMENT-DISPUTED issue was found. Final preflight and delivery results follow below.

The prescribed `deliver2.py --no-push` completed successfully: preflight and compilation
both passed (`OK (dry run)`, candidate commit b7d4d00a9cb). No repairs or extra nodes were needed.
The maintainer's independent delivery review supplies the second reading, as prescribed by
the current direct-delivery brief; no independent worker reading is claimed here.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
