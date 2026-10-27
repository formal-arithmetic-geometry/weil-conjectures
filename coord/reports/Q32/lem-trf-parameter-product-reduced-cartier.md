## Worker report

The module `Sheaf.AlgebraicGeometry.ParameterProductReducedCartier` states
`AlgebraicGeometry.parameter_product_reduced_cartier`, with one `sorry` proof.
It introduces no definitions. The node changes only in `lean`; its mathematical
statement, dependencies and proof plan remain unchanged.

The source was read in the local Travaux de Gabber PDF: VI 1.4 and 1.7,
printed pages 69--70 (PDF pages 75--76), and VIII 4.1.1--4.1.2,
printed page 117 (PDF page 123). VI 1.4 supplies density of the triviality
open, VI 1.7 identifies the regular case with a normal crossings boundary,
and VIII 4.1.2 writes its equation as a product of regular parameters.
The explicit elementary assembly is the node's four-step proof; the relevant
Stacks sources 0BIA, 0AG8 and 07ZU were also read in etale.tex and divisors.tex.
No source-based correction is needed.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A locally Noetherian regular scheme Y | `Y : Scheme.{u}`, `hY : IsRegularScheme Y`; the recorded definition is `IsLocallyNoetherian Y ∧ IsRegular Y`. |
| r ≥ 0 and global sections t_1,...,t_r | `r : ℕ`, `t : Fin r → Γ(Y, ⊤)`. No positivity or nonempty-family hypothesis. |
| At each ordinary point y, B = O_{Y,y} | `∀ y : Y` and the actual structure-sheaf stalk `Y.presheaf.stalk y`. No strict henselization or completion. |
| Nonunit indices J_y | `{j : Fin r // ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j))}`. |
| Nonunit germs are members at distinct positions of a regular parameter system | `hparams` gives `d`, `p : Fin d → Y.presheaf.stalk y`, `IsLocalRing.IsRegularSystemOfParameters (List.ofFn p)`, an embedding `e : J_y ↪ Fin d`, and equality of each selected germ with `p (e j)`. The embedding enforces distinct positions even if the original family repeats an element. |
| Noetherianity needed to type the recorded parameter predicate | Its explicit instance argument is `(@IsRegular.isRegularLocalRing_stalk Y hY.2 y).toIsNoetherian`, supplied by regularity, not an extra hypothesis or a new instance. |
| f is the product of the given sections | Every occurrence is the literal `∏ i, t i`. |
| H = V(f), the principal closed subscheme | `Y.zeroLocusSubscheme {∏ i, t i}` is the existing abbreviation for `(Scheme.IdealSheafData.ofIdealTop (Ideal.span {∏ i, t i})).subscheme`. Its existing inclusion `zeroLocusSubschemeι` is a closed immersion. This is the principal subscheme, not the reduced induced structure on its support. |
| H is reduced | `IsReduced (Y.zeroLocusSubscheme {∏ i, t i})`. |
| H is an effective Cartier divisor | `(Scheme.IdealSheafData.ofIdealTop (Ideal.span {∏ i, t i})).IsInvertible`, the recorded effective Cartier ideal predicate. |
| D(f) = Y minus the support of H is open dense | `Dense (Y.basicOpen (∏ i, t i) : Set Y)`; `basicOpen` is an actual `Y.Opens`, so openness is already in its type. The existing `Scheme.range_zeroLocusSubschemeι_singleton` identifies this open with the complement of H. No extra hypothesis or tautological conclusion is used for openness. |
| B is a nonzero domain at every y | `IsDomain (Y.presheaf.stalk y)`, including its `Nontrivial` parent. |
| Each nonunit germ is prime | `∀ j : Fin r, ¬ IsUnit (...) → Prime (...)`. |
| Distinct selected parameters do not divide one another | `∀ i j : Fin r, i ≠ j → ¬ IsUnit (...) → ¬ IsUnit (...) → ¬ ... ∣ ...`; ordered quantification gives both directions. |
| (f)B equals the ideal of the nonunit product | First `Ideal.span` equality, with the product indexed by the subtype J_y. The germ of the product is the actual ring-homomorphic image of f. |
| This ideal equals the intersection of the selected principal ideals | Second equality `Ideal.span {germ f} = ⨅ j : J_y, Ideal.span {germ (t j.val)}`; together with the first equality this is precisely the displayed chain. |
| The ideal is radical | `(Ideal.span {germ f}).IsRadical`. |
| Its generator is a non-zero-divisor | `germ f ∈ nonZeroDivisors (Y.presheaf.stalk y)`. |
| Empty intersection B and empty product 1 | The empty `iInf` in `Ideal B` is `⊤` and the empty finite product in B is `1`; both are the existing Mathlib operations. |

Recorded statement dependency declarations were opened and read:

| Node | Module and declaration |
| --- | --- |
| pqf-def-locnoeth | `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`; every affine open has a Noetherian section ring. |
| def-weil-regular-scheme | `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`; its upstream factor `AlgebraicGeometry.IsRegular` in `WeilConjectures.AlgebraicGeometry.Regular` gives regular local stalks. |
| def-weil-pbc-regular-system-of-parameters | `WeilConjectures.RingTheory.IsRegularSystemOfParameters`, `IsLocalRing.IsRegularSystemOfParameters`; span is the maximal ideal and list length is the Krull dimension. |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`; closed embedding and surjective stalk maps. The chosen principal closed subscheme uses the existing `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` construction. |
| def-pc-reduced-scheme | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`; its sectionwise definition agrees with the stalkwise form by `isReduced_of_isReduced_stalk` and `isReduced_stalk_of_isReduced`. |
| def-nagata-effective-cartier-ideal | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`; every point has an affine neighborhood with a nonzerodivisor principal ideal. |

All six statement-dependency modules are public imports. The principal-subscheme
construction is also a public import. Proof-only imports are the recorded
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
(`IsRegularLocalRing.isDomain`), the three Mathlib modules recorded in
lem-weil-pbc-localization-at-prime-of-quotient, and
`Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense`
(`Scheme.IdealSheafData.IsInvertible.compl_support_dense`).
The other two proof-only nodes, lem-sfb-transverse-prime-ideal-parameters and
lem-sfb-stalk-nonzerodivisor-cartier-spreading, have no recorded Lean module
on the read base; they are proof obligations only, not notions required to
state this theorem, so no placeholder imports or dependency copies are added.
Their roles remain explicit in the proof docstring and the unchanged DAG.

Edge cases checked before writing: r = 0 makes f = 1, H empty, D(f) = Y,
and both stalk ideals top; Y empty has no stalk obligations and the empty
complement is dense in Y. A field stalk forces J_y empty. If all sections are
units the same argument applies even for r > 0. The local example xy in a
regular two-dimensional local ring gives (xy) = (x) ∩ (y), a reduced crossing,
without requiring H integral. Repetition (x,x) and dependent germs (x,x+y²)
cannot occupy distinct positions in a regular system of parameters. No
positive dimension, global irreducibility, Noetherian rather than locally
Noetherian, finite type, or characteristic hypothesis was added. Scheme and
ring universes are the original single arbitrary u; only the finite index
sets live in Type 0, which excludes no finite family.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: "A function on a regular scheme whose nonunit factors are distinct
  regular parameters defines a reduced effective Cartier divisor with dense
  complement" returned eight hits, including `IsReduced`, its stalk criterion,
  its open-subscheme instance and nilpotence/basic-open facts. None states this
  complete theorem.
- Loogle: `IsRegularSystemOfParameters, IsReduced` returned zero hits (the
  project-defined first identifier is unknown to the Mathlib index).
- grep: `parameter.*radical|radical.*parameter|product.*Cartier|Cartier.*product`
  returned zero Mathlib hits.
- LeanSearch: "A product of distinct regular parameters defines a reduced
  effective Cartier divisor with dense complement" returned eight hits,
  including `IsRegular.prodMk`, `isRegular_mul_iff`, `IsRegular.prod`,
  `MvPolynomial.isRegular_prod_X`, meromorphic-divisor identities and
  `IsReduced.mk`. These concern elements, polynomial coordinates, analytic
  divisors, or the reduced predicate alone, not this scheme theorem.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for parameter/product/
  radical/Cartier patterns found related boundary theorems such as
  `VeryTameBoundaryQuotientCartier` and `PermissibleBoundaryEtaleCharts`, which
  have group-action or blowup hypotheses and different conclusions. Reading
  their declarations confirmed they are not duplicates. The existing
  `Scheme.zeroLocusSubscheme` and `IdealSheafData.ofIdealTop` constructions
  were found and reused.
- Direct rg for `parameter_product_reduced_cartier` in both Lean roots and
  `dag/lean_names_upstream.json`, and the prescribed grep for the node id in
  `lean/WeilConjectures`, found no existing declaration.

No hollow definitions, new nodes, dependency-record repairs, mathematical
faults or disputed statements are present. The compiler initially identified
the inherited Noetherian field spelling; using its actual name
`toIsNoetherian` repairs that elaboration without changing the statement.

## Second reading by Q32

This is the worker's own separate clause-by-clause rereading; the dispatch
brief reserves independent review for the maintainer and prohibits starting
another agent. I reopened the node statement and final module together and
checked each row above. The parameter predicate has exactly the dependency's
maximal-ideal and dimension clauses; the embedding records distinct positions,
not mere membership. Its Noetherian instance is derived from hY, with no
extra assumption. The conclusion retains reducedness, the actual effective
Cartier ideal, dense basic open, domain, prime elements, nondivisibility, both
ideal equalities, radicality and the nonzerodivisor generator. The construction
of H does not assume reducedness. Empty Y, empty J_y and r = 0 are permitted.
The built-in openness and existing complement identity were checked in the
source declarations, rather than silently omitted. No mismatch requiring a
node correction was found. Every theorem proof in the delivery is `sorry`.
