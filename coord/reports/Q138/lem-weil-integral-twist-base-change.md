## Worker report

`Sheaf.Paper.IntegralTwistBaseChange` states
`WeilConjectures.integral_twist_base_change`, with one postponed theorem and no
proof work. The module uses the existing completed coefficients, signed twist
lines, canonical semilinear scalar maps and actual scalar-extension isomorphisms.
Its four helpers only forget structure, apply the inverse-image adjunction, or
specify the normalizations of the signed pullback comparison. They introduce no
replacement tensor product, coefficient sheaf, line, or arbitrary map choice.

The statement matches the node as follows.

* `l : ℕ` and `[Fact l.Prime]` give the prime. `S : Scheme.{u}` and
  `[∀ x : S, Invertible (l : S.residueField x)]` give the scheme with invertible
  prime. There is no finite-field datum or unnecessary characteristic assumption.
* `E` and `F` have `Field`, `Algebra (Padic l)` and `FiniteDimensional` instances.
  `ι : E →ₐ[Padic l] F` represents the specified inclusion. A field embedding
  covers the same data as identifying E with its image in F.
* `completedIntegralCommRingSheafUnrestricted` is the existing inverse limit of
  finite constant coefficient sheaves, retaining commutativity. It is not a
  discrete constant sheaf of the valuation ring.
* `integralTwistLine l E S m` is the recorded `coefficientTwistLine` on
  `purTwistIntegralModule S l E`: unit for zero, tensor power for positive
  exponent, and `SheafOfModules.homObj` into the unit for negative exponent.
  The first line remains the root-limit tensor line with its completed action;
  the existing local-free/completion comparison supplies the identification
  with T tensor over completed Z_l. No identification is assumed as new data.
* The first conjunct, `IsCanonicalTwistScalarMaps ... (twistScalarMaps ...)`,
  unfolds to exactly the coefficient map at zero, root-tensor map at one,
  recursive pure-tensor map for positive powers, and evaluation equation for
  negative powers. This gives the tensor-associativity and dual base-change
  normalizations and their evaluation and tensor-power compatibility.
* The second conjunct identifies the existing isomorphism `twistLineScalarIso`
  on every local pure tensor `b ⊗ x` with `b • twistScalarMaps(m)(x)` for every
  integer `m`. Its type is precisely ordinary extension of the E line to the
  F completed coefficient sheaf, isomorphic to the F line. The implementation
  writes the scalar factor first, the symmetric ordering of the node's tensor.
  Isomorphy is part of the existing comparison's type, not an unproved
  hypothesis added to this theorem.
* The third conjunct quantifies a further finite coefficient field `G` and
  embedding `κ`. It states equality of the actual signed scalar maps for the
  composite inclusion and the two successive inclusions on every section.
  Since the isomorphisms are their balanced linear extensions by the second
  conjunct, this is exactly their tower compatibility under the ordinary
  multiplication associator. It does not just assert existence of an unrelated
  scalar associator.
* The final conjunct quantifies every scheme morphism `h : X ⟶ S`. The
  invertibility instance on X is the inherited invertibility of l. It gives
  coefficient comparisons `αE, αF` characterized by all finite projections and
  the root-limit comparison `τ` characterized by all root projections. The
  signed inverse-image identifications `ρE,ρF` are actual additive-sheaf
  isomorphisms. `IsIntegralTwistInverseComparison` requires coefficient
  semilinearity at every exponent, the unit and root-tensor formulas, tensor
  recursion, and dual evaluation. Its formulas use the true adjunction, so a
  source section at V is sent to a section at the base change of V. The final
  equation is the commuting inverse-image square for the signed scalar maps,
  for every m. Together with the scalar balancing and semilinearity this is
  the asserted scheme naturality of the scalar-extension isomorphisms.

Tensor powers and negative duals are rendered by their recorded definitions.
The recursive positive-power and evaluation equations specify the maps used
for all canonical contractions between opposite signed powers as well: locally
these maps send a generator to its matching generator, and evaluation cancels
opposite factors. There is no independent product or duality convention.

Dependencies read and used (full signatures and source docstrings inspected):

* `def-weil-completed-integral-coefficients`:
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `WeilConjectures.integralConstantToCompletionOfUniverses`, reexporting the
  completed coefficient limit and its commutative-ring version.
* `def-coefficient-twists-detailed`:
  `Sheaf.Paper.CoefficientTwistsDetailed`, `coefficientTwistPower`,
  `coefficientTwistLine`, `integralTwistLine`, `IsCanonicalTwistScalarMaps`,
  `twistScalarMaps`, `twistLineScalarIso`; their existence/uniqueness theorems
  and `twistScalarMaps_composition` give the existing canonical interface.
* `def-pur-sheaf-hom`: upstream
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, the localized-site internal Hom, as used by the
  signed-line definition.
* `lem-pur-twist-sheaf-locally-free`:
  `Sheaf.Paper.PurTwistSheafLocallyFree`,
  `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free` and its root-limit,
  completed-action and integral-tensor helpers; clauses 2 and 3 supply the
  rank-one line and completed coefficient presentation.
* `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`. Object universe u+1
  and morphism universe u are retained, with coefficient/module universe u+1.
* `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`,
  `SheafOfModules.siteSheafTensorTmul` and its publicly imported sectionwise
  tensor/sheafification implementation.
* `lem-pur-integral-twist-line-inverse-image`:
  `Sheaf.Paper.PurIntegralTwistLineInverseImage`,
  `IsPurIntegralCoefficientComparison`, `IsPurRootLimitComparison`,
  `IsPurIntegralTwistComparison`, and `pur_integral_twist_line_inverse_image`.
  This already-landed node is added to stmt_deps because its canonical
  comparison specifications occur explicitly in the naturality conclusion.
* `def-weil-proetale-inverse-image`:
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `proEtaleSheafInverseImage`,
  `proEtaleSheafAdjunction`, and `proEtaleBaseChange`. This already-landed node
  is added to stmt_deps for the same reason.

The proof-only imports retain the recorded tensor/pullback comparison,
finite-free dual pullback and tensor-closed inputs. The complete eight-step
natural-language proof is in the theorem docstring, including local inverse
gluing, all signed contractions, towers and arbitrary scheme naturality.

Edge cases checked: zero exponent is the unit; exponent one is the actual
first line; `Int.negSucc n` covers all negative integers with the dual of
positive exponent n+1; identity inclusions and repeated fields are permitted;
the tower does not require proper extensions; identity scheme maps and the
empty scheme are included. There is no nonempty-scheme assumption or local
basis chosen in the statement. The helpers retain the actual small site and
use the larger sheaf universe, without imposing equality of the site's two
universes. All variables and universes are explicitly bound.

Searches performed:

* `msearch.py leanfinder`, query "Completed integral Tate twist sheaves commute
  with finite coefficient base change, tensor powers and dual evaluation":
  eight light-condensed monoidal/closed-category hits, no matching theorem.
* `msearch.py leansearch`, query "Scalar extension of locally free rank one
  sheaves commutes with signed Tate twist powers and dual evaluation": eight
  localization/module/change-of-rings hits, including
  `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.evalAt_apply`, no completed-sheaf
  twist assertion.
* `msearch.py loogle`, query "Module.Dual.baseChange, TensorProduct.assoc":
  zero hits.
* `msearch.py grep`, query `baseChange.*[Dd]ual|[Dd]ual.*baseChange|tateTwist`
  in `LinearAlgebra`: eight hits in Transvection/Basic and Dual/BaseChange;
  these concern algebraic module duals, not these coefficient sheaves.
* `rg` of the upstream `WeilConjectures` tree for integral/twist/scalar names
  found constant-twist cohomology but no completed signed twist comparison;
  searching the node id and proposed theorem name found no matches.
* `rg` of the side `lean/Sheaf` tree located the existing signed-line and
  scalar-comparison interface, which the module uses rather than duplicating.

No statement correction, disputed statement, new node, or dependency repair is
needed. Only the item's Lean record and the two already-landed statement
prerequisites are changed. The worker is the dispatcher-started single worker;
the maintainer supplies the independent review.

Validation: `scompile.py Q138 lem-weil-integral-twist-base-change
lean/Sheaf/Paper/IntegralTwistBaseChange.lean` passed both the isolated sandbox
and library-module checks, with no errors or unexpected warnings.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
