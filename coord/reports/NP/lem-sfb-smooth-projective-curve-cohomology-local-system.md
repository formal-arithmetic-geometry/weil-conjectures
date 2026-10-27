## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProjectiveCurveCohomologyLocalSystem` states
`AlgebraicGeometry.Etale.localSystem_firstCohomology_smooth_projective_curve`.
Its only theorem has proof `sorry`, as required for stage 2. Five helper definitions
spell out existing constructions and their canonical composites, with real data throughout;
they are all listed in `lean.declarations`. No new independent notion, dependency-module
repair, or statement correction is needed.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X T : Scheme.{u}} (f : X ⟶ T)`. The scheme universe is
  arbitrary, and the geometric fields and base-change schemes use that same universe,
  as in the project's small-etale-site convention.
- Smoothness: `[Smooth f]`, Mathlib's smooth morphism predicate.
- Projectivity in the specified bundle sense: `(hprojective : IsProjectiveBundle f)`,
  using the dependency's canonical relative Proj of the symmetric graded algebra.
  No finite-projective-space or local-freeness hypothesis replaces it.
- Nonnegative integral genus and prime: `(g ell : ℕ) [Fact ell.Prime]`.
  Coefficients are `ULift.{u + 1} (ZMod ell)`, the prime field placed in the coefficient
  universe, without changing its algebra or choosing a root of unity.
- Invertibility in every local ring of T: `hunit : ∀ t : T,
  IsUnit (ell : T.presheaf.stalk t)`.
- Every algebraically closed field and geometric point: `hfibre` quantifies over
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)`.
- The geometric fibre is `pullback f t`, with structural morphism `pullback.snd f t`.
  `IsConnectedCurve` explicitly includes connectedness, nonemptiness and dimension
  exactly one (not merely dimension at most one), as well as separated finite type.
  The remaining conjuncts are `Smooth`, `IsProjectiveBundle`, and `.genus = g`.
  The recorded `Scheme.Hom.genus` is differential genus; its source docstring identifies
  it with `dim H¹(O)` for smooth proper curves by `Scheme.genus_eq_arithmeticGenus`.
  Properness here follows from projective-bundle projectivity. This is the dependency's
  existing genus notion, not a replacement or an additional assumption.
- H = R¹ f_* A_X, as a module sheaf: `curveFirstCohomology ell f` is literally
  degree-one homology of `rightDerivedLowerStarPlus` of the constant regular module
  placed in degree zero. It uses `Sheaf ... (ModuleCat ...)`, the existing constant-ring
  module-valued sheaf encoding also used by the finite-local-system dependency.
- Etale locally A^(2g): the first conjunct supplies a jointly surjective
  `Scheme.Cover.{u} Scheme.etalePrecoverage T` and, on every over-site chart, an
  isomorphism to the constant module `Fin (2 * g) → ULift (ZMod ell)`.
  These are isomorphisms of module sheaves, not just underlying sets or groups.
- Every base change: the second conjunct quantifies over all `T' : Scheme.{u}` and
  `v : T' ⟶ T` and states `IsIso (curveFirstBaseChange ell f v)`.
  Its target is the first cohomology of `pullback.snd f v` with constant coefficients.
  The helper is the homology comparison for exact upper star, followed by degree one
  of `derivedBaseChangeMapPlus` on the canonical pullback square, then the single-functor
  comparison and `constantSheafCompUpperStarIso`. Thus it is the specified BC¹ map.
- The stalk identification is induced by this very map: `curveFirstStalkMap` is
  `(curvePointPullbackStalkIso ...).inv`, followed by global sections of
  `curveFirstBaseChange ell f t`, followed by `curveFirstSectionsIso`.
  The first isomorphism is the canonical identity-point germ
  `ΓIsoSheafFiberOfIsSepClosed`, the canonical `upperStarCompSheafFiberIso`, and the
  identity-composition equality. The second uses the bounded-below/unbounded canonical
  compatibility, exact global sections over Spec Ω, and the Leray isomorphism.
  Its codomain is exactly the dependency `Etale.cohomology` of the constant module
  on the geometric fibre, in degree one.
- The final conjunct says this specific stalk map is invertible and
  `Module.finrank ... (pointedEtaleStalk ...) = 2 * g`.
  Together with the constant local models this is a finite-dimensional stalk of
  dimension 2g, and its displayed identification is linear over A.
- There is no Noetherian, connected-base, positive-genus, odd-prime, or root-of-unity
  assumption. No restriction on the base-change morphism is present.

Dependency declarations read and used (publicly imported directly or through the listed
public interfaces):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-trf-projective-bundle-morphism`:
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`, `AlgebraicGeometry.IsProjectiveBundle`.
- `def-weil-geometric-fibre` and `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, `pullback.snd`.
- `def-weil-geometric-point`, `def-weil-field`, `def-weil-algebraic-closure`:
  `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), and the prescribed inline Spec-field point.
  No algebraic closure of a chosen residue field is necessary: the statement quantifies
  over arbitrary algebraically closed geometric fields as the item expressly requests.
- `def-sc-genus`: `WeilConjectures.AlgebraicGeometry.Curve`, `Scheme.Hom.genus`;
  this same module supplies `IsConnectedCurve`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `def-weil-pbc-direct-image` and `def-weil-pbc-inverse-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.lowerStar`,
  `Etale.rightDerivedLowerStarPlus`, `Etale.upperStar`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  the public `SheafOfModules` category. Here the constant coefficient module sheaves
  use the existing `Sheaf ... (ModuleCat ...)` encoding, as in the direct-image node
  and the finite-local-system dependency, with linear morphisms throughout.
- `def-weil-pbc-derived-exchange`: `WeilConjectures.SixFunctors.BaseChange.Derived`,
  `Etale.derivedBaseChangeMapPlus`.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `Etale.cohomology`.
- `def-weil-pbc-geometric-stalks`: `Sheaf.AlgebraicGeometry.PointedEtaleStalk`,
  `AlgebraicGeometry.pointedEtaleStalk`. Its defining colimit is definitionally the
  `pointSmallEtale.sheafFiber` colimit used by the canonical comparison.

All recorded available proof-dependency modules are imported, using plain imports for
proof-only inputs. Proper and smooth base-change stability are already available through
those imports. The module docstring contains all five proof steps and identifies their
DAG inputs. Additional public imports expose the canonical point, Leray and constant
pullback comparisons that occur in the helper data; none of these is postponed or chosen
from mere existence.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: “First etale cohomology of a smooth projective family of
  genus g curves is locally constant of rank 2g with arbitrary base change”. Eight hits:
  module rank-at-stalk, cotangent cohomology and unrelated locally constant functions;
  none state the node.
- `msearch.py ... loogle`: `"cohomology", "genus"`. Zero hits.
- `msearch.py ... grep`: `[Cc]ohomology.*[Gg]enus|[Ll]ocal[Ss]ystem.*[Cc]urve`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: “First etale cohomology of a smooth projective genus g
  curve family is locally constant of rank twice the genus and commutes with base change”.
  Eight hits, concerning stability of etale/smooth algebra and cotangent cohomology;
  none state the node. Exact wrapper results are in sandbox `searches.jsonl`.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for higher-direct-image, genus and
  local-system terms found the recorded `SmoothProperFiniteCohomologyLocalSystem`,
  `ProperSmoothCurvesPrimeCoefficients`, `Curve.Estimate`, and geometric fibre comparison
  interfaces. The first allows varying finite-dimensional local models; the second
  assumes a Noetherian base and proves constructibility rather than rank 2g; the curve
  computation is over one field, not a family. None is an exact existing match.
- Exact node-id search in upstream Lean has no hit. Exact searches for all six proposed
  declaration names in Mathlib, upstream and Sheaf have no hit.

Edge cases checked before drafting: genus zero gives the constant zero module
(`Fin 0 → A`), not a one-dimensional module. The prime two is admitted by `Fact ell.Prime`.
An empty base admits the empty jointly surjective etale cover, and all geometric-point
conditions are vacuous; no geometric point or connected component is selected in the
statement or definitions. Disconnected bases are allowed and genus is the same prescribed
g on every fibre. Both identity and arbitrary non-flat base changes are included.
The characteristic condition is local invertibility on T, with no global root chosen.

Validation: `scompile.py NP lem-sfb-smooth-projective-curve-cohomology-local-system
<module-path>` passes both sandbox and library module checks (23.0s and 21.8s).
An initial finrank elaboration inferred a set-valued stalk before seeing its sheaf;
explicitly specifying `A := ModuleCat ...` in that expression repaired the issue.
No statement or mathematical hypothesis changed.

## Second reading by NP

I reread the node and the completed module, clause by clause, after compilation.
The source's projective-bundle convention is preserved in both the family and explicit
fibre hypothesis. `IsConnectedCurve` enforces dimension exactly one and nonemptiness;
no zero-dimensional fibre slips through. The existing genus definition agrees with
H¹(O) in this setting. The local models have index `Fin (2 * g)`, the base-change
quantifier includes identity and every scheme morphism, and the cohomology group is the
module-valued `Etale.cohomology` on the actual pullback fibre. I followed the stalk
composite through all three factors and checked it uses `curveFirstBaseChange`, so
no unrelated isomorphism is substituted. The finrank term now specifies module-valued
stalks explicitly. No further mismatch or statement fault was found.
This is a second pass by the same dispatched worker; the dispatcher's instruction
prohibits starting other agents. The maintainer's independent review remains required.
