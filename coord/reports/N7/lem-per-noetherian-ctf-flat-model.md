## Worker report

The delivery states `AlgebraicGeometry.Etale.exists_noetherian_ctf_flat_model` in
`Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel`. It has one theorem, with proof `sorry`,
and no new definitions. The statement and proof plan were checked against Stacks
etale-cohomology.tex, lemma-when-ctf (03TT) and remark-projective-each-degree, and the
node's recorded simultaneous Galois-partition input from ILO XVII 7.3.1 / 7.6.1.

Clause-by-clause rendering:

- Prime ell and Lambda = F_ell: `(l : ℕ) [Fact l.Prime]`, with `ZMod l` as the prime
  field. `(A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
  [Algebra (ZMod l) A]` is precisely the commutative Noetherian Lambda-algebra.
  No finite-set hypothesis, field hypothesis on A, or ell-invertibility on X is added.
- Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with the stated finite
  affine cover by spectra of Noetherian rings. No connectedness of X is assumed.
- The ordinary small-etale derived category: `(K : DerivedCategoryModule A X)` unfolds
  to `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  This is the dependency's module-valued encoding of constant-A module sheaves.
- Membership in D^b_c: `_hK : DerivedCategory.boundedConstructible
  (ModuleCat.{u + 1} A) X K`. This is the existing bounded t-structure property and
  `constructibleHomology`, which tests `Scheme.IsConstructibleSheaf` on every H^q.
  The latter has a finite stratification and locally constant finitely generated
  module stalks on every stratum. The full declaration docstring explicitly identifies
  its Noetherian-module specialization with Stacks constructibility. On Noetherian X,
  every locally closed stratum is constructible, so the extra topological field of the
  upstream stratification excludes no case. This is the node's explicit stalk formulation.
  For finite Lambda it agrees with the finite-value interface of
  `def-weil-pbc-constructible-complexes`; that interface cannot be applied to arbitrary A.
- Specified Tor interval: `(a b : ℤ) (_hab : a ≤ b)` and
  `_hTor : DerivedCategory.hasTorAmplitudeIn A X a b K`. The existing definition tests
  every degree-zero module sheaf F, with no constructibility or finiteness restriction,
  using `Etale.derivedTensor` and `IsZero` of cohomology for q<a or b<q. Together with
  bounded constructibility this is exactly D^b_ctf of the item; no additional finite-Tor
  witness is required.
- Representing cochain complex: `∃ F : CochainComplex
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ` and
  `Nonempty (DerivedCategory.Q.obj F ≅ K)`.
- Support in [a,b]: `∀ q : ℤ, (q < a ∨ b < q) → IsZero (F.X q)`.
- Every term flat and constructible: `∀ q, ObjectProperty.flat (F.X q) ∧
  Scheme.IsConstructibleSheaf (F.X q)`. Flatness is exactness of tensoring (the
  existing predicate tests both tensor orders, equivalent by the symmetric tensor).
- One finite locally closed stratification: `∃ S : Scheme.FiniteLocallyClosedStratification X`.
  Its inherited fields give a finite disjoint locally closed partition covering X;
  `domain`, `immersion`, `isImmersion`, `range_immersion` realize its subschemes.
- Reduced and connected strata: `∀ i, IsReduced (S.domain i)` and
  `∀ i, ∃ hS : ConnectedSpace (S.domain i), ...`. ConnectedSpace includes nonemptiness.
- A connected finite etale Galois cover for each stratum: `∃ V : (S.domain i).FiniteEtale`,
  `PreGaloisCategory.IsGalois V` using the canonical Galois-category instance supplied
  with hS, and `ConnectedSpace V.obj.left`. The explicit instance argument is needed
  because hS is existential evidence rather than an ambient instance. The recorded
  `Scheme.FiniteEtale.isGalois_iff` identifies this intrinsic predicate with the simply
  transitive automorphism action on every geometric fibre; finite etale connected
  objects over a connected base are surjective. No point is selected in the statement.
- Simultaneous constant finite-projective values: the cover V is quantified before
  `∀ q, a ≤ q → q ≤ b → ∃ M`, and M satisfies `Module.Finite A M` and
  `Module.Projective A M`. The isomorphism is from
  `(upperStar _ (V.obj.hom ≫ S.immersion i)).obj (F.X q)` to the actual constant sheaf
  `(constantSheaf V.obj.left.smallEtaleTopology (ModuleCat A)).obj M`.
  Pullback along the composite is the canonical composition of the two restrictions.
  Finite projectivity is exactly being a direct summand of finite free: split any
  finite generating epimorphism. Zero terms also satisfy this clause by M=0.

Dependency declarations read and used:

- Mathlib: `Scheme`, `Scheme.Hom` (AlgebraicGeometry.Scheme),
  `IsNoetherianRing` (RingTheory.Noetherian.Defs), `Scheme.smallEtaleTopology` and
  `Scheme.Etale` (AlgebraicGeometry.Sites.Etale), `Module.Finite`
  (RingTheory.Finiteness.Defs), `CochainComplex` (Algebra.Homology.HomologicalComplex),
  `ConnectedSpace` (Topology.Connected.Basic), `IsReduced` (AlgebraicGeometry.Properties),
  and `PreGaloisCategory.IsGalois` (CategoryTheory.Galois.GaloisObjects).
- `DerivedCategoryModule` and `DerivedCategory.hasTorAmplitudeIn` from
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients (also the published
  WeilConjectures.AlgebraicGeometry.DerivedCategories source read via scompile --source);
  `derivedTensor` is the dependency recorded in Etale.Derived.Tensor.
- `Scheme.IsConstructibleSheaf` from WeilConjectures.ConstructibleSheaf.Defs and
  `DerivedCategory.boundedConstructible` from
  WeilConjectures.CategoryTheory.DerivedCategory.Constructible. Their already recorded
  nodes `def-constructible-constructible` and `def-sf-setting` were added to stmt_deps
  to cite the existing arbitrary-coefficient interfaces, as permitted by §5.
- `Scheme.FiniteLocallyClosedStratification` from
  Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification and `Etale.upperStar` from
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs.
- The module-sheaf locally constant finite-type record
  SheafOfModules.IsLocallyConstantFiniteTypeModules was read in its recorded module.
  It takes an equal-universe general site and cannot directly accept the small-etale
  site with object universe u+1 and morphism universe u. The existing upstream
  module-valued `IsFiniteLocallyConstantSheaf` in the constructible predicate already
  gives the node's equivalent stalk formulation without identifying these universes.
  No second general-site notion is introduced.
- `CategoryTheory.ringedSiteModules` from Sheaf.CategoryTheory.RingedSiteModules
  was read; the derived-category dependency explicitly uses the equivalent module-valued
  encoding, which is retained throughout this statement.

Proof-only imports include the recorded Noetherian Serre theorem, lifting-class flat-model
resolution, flat pullback, constant geometric stalk, Noetherian submodule finiteness and
finite-presentation/flat implies projective. The two proof-only nodes
`lem-per-noetherian-constructible-flat-lifting` and
`lem-per-noetherian-constructible-galois-partition` have no recorded Lean module at this
reading, so there is no module to import. Neither is a statement prerequisite. Their exact
uses are retained in the theorem's six-step proof docstring. No claim of their proof is made.

Edge cases checked: the empty scheme has zero module sheaves and zero derived category;
S.n=0 is permitted without a Nonempty index binder. A nonempty stratum and cover are
required exactly where the conclusion calls them connected. The zero algebra and zero
complex are allowed. The interval a=b, negative endpoints, zero terms inside the interval,
and disconnected X are included. Covers are chosen once per stratum, not once per degree;
only the finite interval is trivialized. No differential trivialization or projectivity in
the category of sheaves is asserted. The scheme universe u and module/ring universe u+1
follow the existing derived category with the site's distinct object/morphism universes.

Searches for existing statements:

- msearch LeanSearch, query “A bounded constructible etale complex of finite Tor amplitude
  over a Noetherian ring has a bounded flat constructible model”: eight results on ordinary
  smooth/flat algebras and flat modules; no etale constructible model.
- msearch LeanFinder, query “A bounded constructible etale complex of finite Tor amplitude
  over a Noetherian coefficient ring has a bounded flat constructible model with finite
  projective constant values on Galois strata”: eight algebraic smooth/etale results; no match.
- msearch Loogle, `DerivedCategory, CochainComplex`: twelve localization/single-functor
  results including Q; none supplies constructible flat models or Galois strata.
- msearch grep `constructible|flatResolution` in Mathlib/Algebra/Category: zero hits.
- rg in upstream WeilConjectures, side lean/Sheaf and dag/lean_names_upstream.json for
  `lem-per-noetherian-ctf-flat-model`, Noetherian flat-model names and Galois partitions:
  no exact declaration. Existing EtaleFlatConstructibleModel requires `[Finite Λ]` and
  gives no simultaneous Galois/projective-value conclusion, so it is not this statement.
  The upstream generic FlatModelOfClass theorem is a proof ingredient, not the specialized
  theorem with its complete geometric conclusion.

No statement correction and no STATEMENT-DISPUTED issue. Compilation through scompile.py
passed for both its sandbox probe (3.7 seconds) and the named module (3.4 seconds), without
errors or warnings. Initial wrong Mathlib projective-module import was removed; the
existing coefficient imports already expose Module.Projective.

## Second reading by N7

Self-check with the original node and final Lean file open; the dispatch explicitly forbids
starting another agent, and the maintainer supplies the independent review. This section
records the local second pass, not an independent worker's approval.

Each hypothesis and conclusion was checked in the mapping above. The earlier finite-ring
constructibility API cannot express arbitrary Noetherian A; the final signature instead
uses the existing arbitrary-coefficient predicates and cites their owning nodes. All
strata are connected and reduced, V is finite etale and Galois, and the cover quantifier
precedes all degrees. The module is the ordinary derived category, not the completed or
pro-etale category. The connectedness proof hS is used only to select the canonical
Galois-category instance and does not add a hypothesis to the theorem. IsZero outside
the interval represents zero terms invariantly under isomorphism. Finite plus projective
values is exactly the parenthetical direct-summand condition. No mismatch requiring a
node correction was found; no extra statement or definition is delivered.
