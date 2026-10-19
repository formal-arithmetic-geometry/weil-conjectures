## Worker report

Current return repaired: immutable head `8eecadf11f98` was returned for H1 because
the delivery lacked its report and both required report sections. The retained
packet already restores `report.md`, including `## Worker report` and
`## Second reading by Q09`. Its initial dry run passed as `c4f372e8fb`, with the
report explicitly listed among the staged files and a clean compile. This repair
retains the saved Lean module and node record and delivers the restored report;
it is not an unchanged re-push of the returned head. The historical mathematical
repair below explains the retained statement.

Repair of the independent stage-2 return on immutable head `900d22f24fcf`:
H3 identified missing assertions after étale base change, a restriction of geometric
fields to universe `u`, and missing coordinate-equation independence. The saved packet
was inspected first and its required initial `deliver2.py --no-push` passed as commit
`7d6a268d1c`. That mechanical pass did not resolve the mathematical return. The existing
module and node record have been retained and repaired, rather than repushed unchanged.
The delivery wrapper rebases the packet on current `newtargets-dag`.

The module `Sheaf.TraceFormula.CoordinateMaximalBranchStratum` states
`AlgebraicGeometry.Scheme.IdealSheafData.coordinate_maximal_branch_stratum`.
It has one theorem, with proof `sorry`, and no new definitions or axioms. The source
was reread in ILO, Exposé VIII, 4.1.6 and 4.1.8, printed p.118, with the coordinate
interpretation in 4.2.4, p.119. The docstring now records all five DAG proof steps.
The natural-language statement is unchanged; no statement correction is needed.

Every hypothesis and object is rendered as follows:

| Node | Lean |
| --- | --- |
| Regular locally Noetherian scheme `U` | `[IsLocallyNoetherian U]` and `hregular : ∀ x, ∃ V : U.affineOpens, x ∈ V.1 ∧ IsRegularRing Γ(U,V)`; this is exactly the scheme form recorded by `def-weil-regular-scheme`. |
| `s ≥ 1`, regular functions | `hs : 1 ≤ s`, `t : Fin s → Γ(U, ⊤)`. |
| At every point, precisely the vanishing germs are distinct members of a regular system | `hcoord` supplies a Noetherian stalk and lists `q l`, with `IsRegularSystemOfParameters q`, `l.Sublist q`, germ-in-maximal-ideal iff germ-in-`l` for every index, and inequality of the germs for distinct vanishing indices. Membership in the maximal ideal is exactly zero in the residue field. The list `q` spans the maximal ideal and has length equal to Krull dimension by the imported definition. Extra entries in `l` cause no restriction: it can always be chosen as the selected entries of `q`. |
| Closed subschemes `D_U`, `C` | `D := ofIdealTop (Ideal.span {∏ j, t j})` and `C := ofIdealTop (Ideal.span (Set.range t))`, with their actual `subscheme` constructions. |
| Branch count | `b x := Nat.card {j // germ (t j) ∈ maximalIdeal _}`. |

Every conclusion is rendered as follows:

| Node | Lean |
| --- | --- |
| Geometric point with algebraically closed field | `Ω : Type (max u v)`, `[Field Ω] [IsAlgClosed Ω]`, `x : U`, `ι : U.residueField x →+* Ω`. A geometric point is equivalently its underlying point and residue-field embedding. This avoids requiring `Spec Ω` and `U` to belong to the same scheme category. `v` is arbitrary, so fields in any larger universe are included; `v = 0` includes the original `u` case. No smallness assumption or equality of universes is added. |
| Geometric coordinate count and intrinsic branch count | The first clause says `D.ncBranchCount x = b x` and `Nat.card {j // ι (U.Γevaluation x (t j)) = 0} = b x`. The imported `ncBranchCount` is the project's intrinsic geometric branch interface, not a private coordinate-count definition. Its geometric interpretation is explained by the strict-local minimal-prime argument in proof steps 1–2. |
| Zero branches off `D_U` | `∀ x, b x = 0 ↔ x ∉ D.support`. |
| Bound | `∀ x, b x ≤ s`. |
| Every integer stratum | `∀ (k : ℤ) (x : U), k ≤ (b x : ℤ) ↔ k ≤ 0 ∨ ∃ J : Finset (Fin s), k = J.card ∧ x ∈ (ofIdealTop (Ideal.span (Set.range (fun j : {j // j ∈ J} ↦ t j.1)))).support`. Thus all of `U` for `k ≤ 0`, and the empty locus for `k > s`. The finite union is represented by the existential over finite subsets. |
| Deepest locus | `∀ x, b x = s ↔ x ∈ C.support`. |
| Regular reduced closed subscheme | `IsReduced C.subscheme` and the affine-local `IsRegularRing` condition for every point of `C.subscheme`. |
| Empty center allowed; attainment iff nonempty | `(∃ x, b x = s) ↔ Nonempty C.subscheme`; no nonemptiness hypothesis is imposed. |
| Same assertions after EVERY étale base change | For arbitrary `e : W ⟶ U` with `[Etale e]`, the final clause defines the actual pulled functions `tW j := e.appTop (t j)` and their count `bW`. It asserts locally Noetherian and regular `W`, the full parameter hypothesis for `tW`, and equality of `D.comap e`, `C.comap e` with the product and intersection ideals of `tW`. It asserts `bW w = b (e w)`; intrinsic and geometric count formulas with `Ω : Type (max u v)`; the off-divisor zero criterion; the bound; the full integer-stratum union formula; the deepest locus formula; reducedness and regularity of the pulled center; and attainment iff that center is nonempty. These were not all present in the returned version. |
| Independence of coordinate equations | The last conjunction inside the base-change clause quantifies over ANY `r ≥ 1` and `a : Fin r → Γ(W, ⊤)` satisfying the identical parameter hypothesis. If its product ideal defines the same closed subscheme `D.comap e`, its coordinate count equals `bW` at every point. The number `r` need not equal `s`, and no ordering, unit multiplier, or permutation is prescribed. Taking `W = U` and `e = 𝟙 U` gives independence on the original chart; it is also explicit after every étale base change. |

Dependency declarations read and used:

- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing`, `IsRegularLocalRing`;
  the recorded scheme specialization of `def-weil-regular-scheme` is used verbatim.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` / `Subscheme`: closed immersions,
  `Scheme.IdealSheafData.ofIdealTop`, `support`, `subscheme`, `comap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount`:
  `Scheme.IdealSheafData.HasNCBranchChart`, `ncBranchCount`; this landed definition
  remains the only added statement dependency from the saved packet.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters` (actual maximal-ideal span and dimension).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Γevaluation`.
  `Scheme.Hom.appTop` is the canonical pullback of global functions.

Edge cases checked: `s = 1`; empty `U` and empty deepest center; points off the divisor;
negative `k`, `k = 0`, `k = s`, `k > s`; identity and empty étale base changes;
étale opens missing the original deepest locus (attainment is tested on the PULLED
center); alternative presentations with different numbers of globally listed factors,
including unit factors and permutations; and geometric fields larger than universe `u`.
The empty coordinate intersection uses the ideal spanned by an empty family, namely
`⊥`, whose vanishing locus is all of `U` (the saved report incorrectly called it the
unit ideal). An empty divisor, by contrast, is represented by a unit product.

Searches retained from the saved packet and repeated where relevant:

- `msearch.py ... leanfinder "coordinate description of maximal branch stratum in a regular scheme"`:
  generic affine-cover, stalk and residue-field declarations; no matching theorem.
- `msearch.py ... loogle "IsRegularRing, IsLocallyNoetherian, ncBranchCount, IdealSheafData"`:
  no hits; service reported `IsLocallyNoetherian` unknown.
- `msearch.py ... grep "coordinate.*branch|branch.*stratum|normalCrossing" AlgebraicGeometry`:
  zero hits.
- During repair, `leanfinder "coordinate normal crossings branch count is invariant under choice of regular parameter equations and etale base change"`:
  eight hits about standard smooth and étale polynomial presentations, no branch-stratum theorem.
- During repair, `loogle "IsRegularRing, Ideal.span"`: zero hits.
- During repair, `grep "coordinate.*branch|branch.*stratum" AlgebraicGeometry`: zero hits.
- `rg` over upstream `WeilConjectures` and published `lean/Sheaf` for
  `coordinate_maximal_branch_stratum|lem-trf-nc-coordinate-max-stratum`: only the
  downstream blowup docstring, no existing theorem to reuse.

No `STATEMENT-DISPUTED` issue or node statement fault was found. No new nodes or
dependency modules are introduced. Only the original module, its Lean record, and this
report are repaired. The wrapper supplies current-base delivery bookkeeping.

## Second reading by Q09

For the H1 repair, I reopened the complete node and Lean file and checked the
clause correspondence in the tables above, including the full base-change and
alternative-coordinate conjunctions. I also compared the packet with current
main: the node differs only in `lean` and the previously added branch-count
dependency in `stmt_deps`. The signature in `lean.statement` matches the file
verbatim, all Lean lines are at most 100 characters, `autoImplicit` is false,
and the sole theorem proof remains `sorry`. Both required report sections are
present. No further statement mismatch was found in this check and no Lean
change was made for the H1 return. The dry run confirms that the report is
included in the delivery; the maintainer supplies the independent review.

This repair's self-check reread the node against the final signature, including the
entire final conjunction. It found and corrected the three returned mismatches:
all étale assertions are now present, larger geometric fields are included through
residue-field embeddings, and arbitrary coordinate-equation comparison is explicit.
The first compile found a shadowed list variable `r` in the alternative-coordinate
clause; the sublist is now named `l`, distinct from the number of alternative factors.
The node's hypotheses, product and center constructions, integer boundary cases,
empty-center case, and every pulled-back conclusion were checked again. The natural
statement was not changed. This is a worker self-check; the maintainer performs the
independent review under the current direct-delivery workflow.
