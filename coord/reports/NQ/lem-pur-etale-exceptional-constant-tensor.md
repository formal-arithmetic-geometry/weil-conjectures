## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor` states
`AlgebraicGeometry.Etale.exceptionalConstantTensor`, with `sorry` as its sole postponed proof.
The three helper definitions have real data: they restrict the existing derived tensor to
constant coefficients, descend the existing constant-sheaf pullback isomorphism, and compose
the existing compactification projection map with these identifications and signed symmetries.
No new independent notion, dependency module, or other DAG theorem is stated.

The inherited attempt was checked against the current node, each recorded statement
dependency, their source declarations, and the cited Zheng passages. The statement and
canonical helper constructions are retained. The derived-category dependency import is
now public, `autoImplicit` is explicitly disabled, and the theorem docstring contains the
complete ten-step natural-language proof from the DAG. A fresh second reader must review
the current delivery independently.

The hypothesis and clause correspondence is:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Algebraically closed field k, characteristic p>0 | `(k : Type u) [Field k] [IsAlgClosed k]`, `[Fact p.Prime] [CharP k p]`. A positive field characteristic is prime. |
| Prime ell different from p | `[Fact ell.Prime]`, `hne : ell ≠ p`. |
| X,Y finite type over k | Structure maps `xk`, `yk`, each with `LocallyOfFiniteType` and `QuasiCompact`. |
| f a separated finite-type k-morphism | `f : X ⟶ Y`, `hf : f ≫ yk = xk`, `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. |
| No separatedness of Y over k | No separatedness instance on `yk` is required. |
| Fix a compactification | `c : Compactification f`, the existing data `Z`, proper `g`, open `i`, and `comm`. |
| Finite commutative ell-primary coefficient ring | `(C : Type (u + 1)) [CommRing C] [Finite C]` and `(∃ n : ℕ, ∀ z : C, (ell : C)^n*z=0)`. |
| Ordinary unbounded D(T_et,C) | `DerivedCategoryModule C T`, the existing `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} C))`. |
| F=Rp_* j_! | `rightDerivedLowerShriekOfCompactification (ModuleCat.{u+1} C) c`, defined as the exact-derived open extension followed by total right-derived proper pushforward. |
| Nonnegative N_f depending only on f, independent of C | `∃ Nf : ℕ, ∀ c C [CommRing C] [Finite C], ...`; the existential precedes coefficients and compactifications. |
| F sends D≤a into D≤a+N_f | `∀ a K, DerivedCategory.IsLE K a → DerivedCategory.IsLE (F.obj K) (a + Nf)`. `DerivedCategory.isLE_iff` identifies this with cohomology vanishing above the bound. |
| Any nonnegative geometric-fibre dimension bound d gives N_f=2d | `∀ d : ℕ`, the dimension inequality on the pullback along `Spec (AlgebraicClosure (Y.residueField y)) → Y` for every y, followed by the same implication with `(a + 2*(d:ℤ))`. |
| Fix any right adjoint G and counit | `∀ G (adj : F ⊣ G)`, with `adj.counit` in the concluding equation. Existence is the already recorded exceptional-adjoint theorem. |
| Arbitrary unbounded V in D(C-Mod) | `V : DerivedCategory (ModuleCat.{u+1} C)`, with no boundedness, perfectness, or Tor hypothesis. |
| V_T is termwise constant | `(constantSheaf T.smallEtaleTopology (ModuleCat C)).mapDerivedCategory`, used by `exceptionalCoefficientTensor`. |
| Canonical V_Y tensor F(K) → F(V_X tensor K) invertible for all V,K | A natural isomorphism `P` of curried bifunctors, with `(P.hom.app K).app V = exceptionalConstantProjectionMap C c V K`. |
| Canonical V_X tensor G(M) → G(V_Y tensor M) invertible for all V,M | A natural isomorphism `A` of curried bifunctors, characterized by `adj.homEquiv` applied to `P.inv` followed by tensoring the counit. |
| The second map is the specified adjunction transpose | Its equality uses exactly `(P.inv.app (G.obj M)).app V ≫ tensor.map (adj.counit.app M)`. |
| Naturality in both variables | `P` and `A` are isomorphisms in curried functor categories, rather than unrelated objectwise isomorphisms. |
| Independence of resolutions | The first comparison is a fixed composite of existing localization-defined maps on derived categories; the second is characterized by transposition of that map and the fixed counit. No representative or resolution is a parameter. |
| Tensor for G only by constant coefficient complexes | Both bifunctors restrict the tensor coefficient through the constant-sheaf functor. |

Recorded dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is a convention record. Its finite-type and separated
  notions are Mathlib `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated`; `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` is imported.
- `def-weil-compactifications-refinements`:
  `WeilConjectures.Compactification.Refinement`, `AlgebraicGeometry.Compactification`
  (defined in `WeilConjectures.Compactification.Defs`) and its refinement structure.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, using
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `thm-amb-etale-exceptional-adjoint`: `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`,
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  Its Noetherian/compact hypotheses follow from finite type over k and properness of the
  compactification; no additional hypotheses are put in this signature.
- `def-sbc-standard-tstructure-derived-category`: Mathlib
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsLE`, and `DerivedCategory.isLE_iff`,
  from `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `def-weil-abstract-derived-category`: `DerivedCategory` from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` from
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor` from
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.
- The inherited sandbox added the already landed `def-weil-geometric-fibre` and
  `lem-kun-tensor-sym` to statement dependencies. Their exact recorded declarations are
  `CategoryTheory.Limits.pullback` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, specialized along the
  algebraic-closure point as prescribed by the node, and
  `AlgebraicGeometry.Etale.derivedTensorSymmetry` from
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`. Both records are usable.

The canonical helpers additionally use `projectionMapOfCompactification` from
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`,
`leftDerivedUpperStarIsoMapDerivedCategory` from
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` and
`Scheme.upperStarConstantSheafIso` from `WeilConjectures.ConstructibleSheaf.Defs`, together
with the flat-module instances from
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`, and the existing Mathlib
`Functor.mapDerivedCategoryCompIso` and `Functor.mapDerivedCategoryNatIso`. No arbitrary
map or merely inhabited isomorphism is substituted for a canonical construction.

The theorem docstring reproduces all ten steps of the DAG proof in full: the fibre bound; the sheaf
amplitude; brutal-truncation telescopes; proper/open projection; compact generators and
finite Tor amplitude; preservation of sums by the right adjoint; compatible shifts;
projection shift/unit compatibility; the counit mate; and propagation from the coefficient
unit by free generation. Stated proof-dependency modules are imported without `public`.
The finite-ring compact-generator node currently has no Lean statement and is a proof-only
prerequisite: it is not restated in this delivery.

Edge cases checked: empty X or Y; vacuous fibre bound on empty Y; zero complexes and zero
ring; annihilator exponent n=0 (forcing the zero ring); N_f=0 and d=0; all integer a,
including negative bounds; the identity map; nonseparated Y; nonregular finite C; and
unbounded V,K,M. The input `IsLE K a` is essential in the identity case. The explicit universe
u follows the existing small-etale-site framework and `ModuleCat.{u+1}` convention; no
independent site-universe equality is imposed. All binders and universes are explicit.

Source inspected: Zheng, Theorem 2.18(2), Corollary 2.19, Construction 2.26 and
Proposition 2.29(2), in the local PDF named by the node. They supply the compact-support
projection, amplitude and the adjunction-transpose construction for ordinary unbounded
categories. The DAG supplies an independent compact-generation proof for the constant
coefficient case. No node statement correction is necessary; no STATEMENT-DISPUTED remains.

Duplicate searches were repeated using the prescribed `msearch.py` LeanFinder query
"Unbounded etale exceptional inverse image commutes with tensor of arbitrary constant
coefficient complexes", Loogle query `"rightDerivedLowerShriek"`, and Mathlib grep query
`exceptional.*[Tt]ensor|constant.*projection|constant.*[Tt]ensor`. LeanFinder returned eight algebraic-etaleness
base-change and Kaehler-differential hits, none about exceptional inverse image.
Loogle returned zero hits; grep returned seven unrelated PiTensorProduct/computability/tactic/analysis hits. Actual
outputs are recorded in `searches.jsonl`. Direct `rg` over upstream `WeilConjectures` and
project `lean/Sheaf` for the node id and all four declaration names returned no duplicate.
The inherited searches also found only the ordinary compactification projection map,
constant-sheaf pullback, and derived symmetry, all reused here.

Validation uses only the prescribed `scompile.py` wrapper and `deliver2.py --no-push`.
The first current dry run compiled both sandbox and library forms, exposing a docstring
spacing warning; its extra blank line was removed. The final dry run must print OK before
this item is handed to the independent second reader. It is intentionally not pushed by
this worker, and no independent second-reading section is claimed here.

## Second reading by NQ

I opened the node, its source passages, the complete Lean module, and every recorded
statement dependency. The item-by-item correspondence is:

* The algebraically closed characteristic-\(p\) field and distinct prime \(\ell\) are
  `(k : Type u) [Field k] [IsAlgClosed k] (p ell : Nat) [Fact p.Prime]
  [Fact ell.Prime] [CharP k p] (hne : ell ≠ p)`.
* The finite-type \(k\)-schemes and \(k\)-morphism are rendered by `X Y : Scheme.{u}`,
  structure maps `xk`, `yk`, their `LocallyOfFiniteType` and `QuasiCompact`
  instances, `f : X ⟶ Y`, and `hf : f ≫ yk = xk`, with `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f`. There is deliberately no
  separatedness instance for `yk`.
* The fixed compactification is `c : Compactification f`; its `Z`, open immersion,
  proper map, and factorization are the recorded `Compactification` fields, used by
  `rightDerivedLowerShriekOfCompactification`.
* A finite commutative \(\ell\)-primary coefficient ring is `(C : Type (u + 1))
  [CommRing C] [Finite C]` together with `∃ n, ∀ z, (ell : C)^n * z = 0`.
* The ordinary unbounded categories and constant complexes are exactly
  `DerivedCategoryModule C T` and the `constantSheaf ... .mapDerivedCategory` used by
  `exceptionalCoefficientTensor`; no boundedness, perfectness, or resolution parameter
  occurs.
* The coefficient-uniform amplitude clause is the first conjunct after
  `∃ Nf : Nat`: for every `c`, `C`, annihilator witness, integer `a`, and `K`, an
  `IsLE K a` premise yields `IsLE (Rf_! K) (a + Nf)`. The next conjunct quantifies
  `d : Nat`, requires the stated bound on every geometric fibre represented by the
  recorded `pullback` along the algebraic-closure point, and gives `a + 2*d`.
* The final conjunct quantifies an arbitrary `G` and an adjunction `adj : F ⊣ G`, then
  supplies `P` with source `F ⋙ exceptionalCoefficientTensor C Y` and target the
  constant-tensor functor followed by `F`. Its pointwise equation is precisely
  `exceptionalConstantProjectionMap C c V K`. It supplies `A` with source `G`
  followed by constant tensor on `X`, target constant tensor on `Y` followed by
  `G`, and its pointwise equation is `adj.homEquiv` applied to `P.inv` followed by
  the counit tensor map. Thus the second comparison is exactly the specified adjunction
  transpose. The natural-isomorphism types preserve naturality in both variables, and no
  arbitrary sheaf tensor formula for `G` is asserted.

The quantifier order `∃ Nf, ∀ c C` expresses that the bound depends only on `f`, as
the node requires, while allowing every fixed compactification. The coefficient universe
`Type (u + 1)` is the project-wide small-etale/module convention used by the recorded
derived-category declaration, not an additional mathematical restriction. Empty schemes,
empty fibre index (vacuous bound over an empty `Y`), zero complexes, the zero ring (the
case `n = 0`), `d = 0`, `Nf = 0`, negative `a`, identity `f`, nonseparated `Y`,
nonregular finite `C`, and unbounded `V`, `K`, and `M` were checked against the
binders. None is excluded by the Lean signature.

I reread Zheng Theorem 2.18(2), Corollary 2.19, Construction 2.26, and Proposition 2.29(2)
from the local PDF text, and searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with
`rg`; the prescribed LeanFinder/Loogle/grep searches are recorded in `searches.jsonl`.
The dependency declarations `Compactification`, `DerivedCategoryModule`,
`constantSheaf`, `derivedTensor`, `pullback`, and `derivedTensorSymmetry` were
opened and used as recorded. No existing declaration states this theorem or duplicates any
helper.

No mismatch was found. I made no source or statement change. In particular, the fibre
bound is the canonical geometric-fibre pullback, the projection helper is a composite of
the recorded projection, pullback, and signed tensor-symmetry maps, and the mate uses the
fixed counit. The only delivery changes are the worker's recorded Lean declaration and the
two necessary landed statement dependencies (`def-weil-geometric-fibre` and
`lem-kun-tensor-sym`).

