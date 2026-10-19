## Worker report

The module `Sheaf.RingTheory.LocalGradedFlatModuleFinitePresentation` states
`WeilConjectures.local_graded_flat_module_finite_presentation`, the Stacks Project Tag 053C
lemma, with `sorry`. The mathematical statement is unchanged. The preserved sandbox contained
no earlier module or node copy: the previous refusal concerned the already accepted stage-1
split, whereas the shared node still has no stage-2 Lean record. This packet supplies that
record and its module.

I read the item, its four statement dependencies and recorded declarations, the source
statement and proof in `literature/stacks-project/more-algebra.tex`, lines 5856--5909, and the
recorded proof prerequisites. The theorem's docstring gives all four proof steps with their
DAG references. Every declared universe and variable is explicit; `autoImplicit` is disabled.

The node's hypotheses and clauses correspond to the Lean as follows:

| Node clause | Lean rendering |
| --- | --- |
| Nonzero commutative local ring R | `{R : Type u} [CommRing R] [IsLocalRing R]`; Mathlib's `IsLocalRing` extends `Nontrivial R` and is equivalent to existence of exactly one maximal ideal for a commutative ring. |
| n ≥ 0 variables, including n = 0 | `(n : ℕ)` and variable set `Fin n`. |
| Positive integer weights w_i | `(ω : Fin n → ℕ) (hω : ∀ i : Fin n, 0 < ω i)`; positive natural numbers are precisely positive integers. |
| P = R[x_1,...,x_n] | `MvPolynomial (Fin n) R`, with its canonical R-algebra structure. |
| Degree-d polynomials are the R-span of monomials of weighted degree d | `MvPolynomial.weightedHomogeneousSubmodule R (fun i : Fin n ↦ (ω i : ℤ)) d`; its definition requires every nonzero coefficient's exponent to have `Finsupp.weight` equal to d. `Finsupp.weight` sums exponent times weight, so finite monomial expansion gives precisely the specified span. |
| R has degree zero and x_i has degree w_i | A constant's exponent vector has weight zero, and the exponent vector of x_i has weight `ω i`. This follows directly from the same Mathlib definition, rather than from an extra assumption. |
| P_d = 0 for d < 0 | Every exponent is a natural number and every weight is positive; the integer weight of every monomial is nonnegative. Hence a negative weighted homogeneous polynomial has no nonzero coefficients. |
| L is a P-module | `{L : Type v} [AddCommGroup L] [Module (MvPolynomial (Fin n) R) L]`. |
| The coefficient-ring action on L is the restriction of its P-action | `[Module R L] [IsScalarTower R (MvPolynomial (Fin n) R) L]`; the tower expresses compatibility with the canonical constant-polynomial map, not an extra flatness or finiteness condition. |
| Internal grading by R-submodules, indexed by every integer | `(Ldeg : ℤ → Submodule R L) (hLinternal : DirectSum.IsInternal Ldeg)`; `IsInternal` is bijectivity of the canonical additive direct-sum map to L, so includes both finite homogeneous decompositions and uniqueness. |
| P_e L_d ⊆ L_(e+d) | `hgraded`, quantified over all `e d : ℤ`, polynomials `p`, and elements `x`, with membership in the canonical weighted homogeneous submodule and `Ldeg d` implying `p • x ∈ Ldeg (e + d)`. |
| L finite over P | `[Module.Finite (MvPolynomial (Fin n) R) L]`. |
| L flat over R | `[Module.Flat R L]`, not flatness over P. |
| L finitely presented over P | Conclusion `Module.FinitePresentation (MvPolynomial (Fin n) R) L`. |

The four dependency interfaces are used without copies: `MvPolynomial` from
`Mathlib.Algebra.MvPolynomial.Basic` (`def-weil-pbc-mv-polynomial-ring`), `Module.Finite`
from `Mathlib.RingTheory.Finiteness.Defs` (`def-weil-finitely-generated-module`),
`Module.Flat` from `Mathlib.RingTheory.Flat.Basic`, publicly exposed through the recorded
`Mathlib.RingTheory.RingHom.Flat` (`def-weil-pbc-flat-ring-map`), and
`Module.FinitePresentation` from `Mathlib.Algebra.Module.FinitePresentation`
(`def-sc-finitely-presented-module`). The other statement infrastructure is Mathlib's
`IsLocalRing`, `Submodule`, `DirectSum.IsInternal`, and
`MvPolynomial.weightedHomogeneousSubmodule`; no helper notion is redeclared.

Proof-only imports cover every available proof prerequisite: `Mathlib.RingTheory.FiniteType`
for `Algebra.FiniteType.isNoetherianRing`; `Mathlib.RingTheory.Flat.Equalizer` for
`LinearMap.lTensor_injective_of_exact_of_flat`; `Mathlib.RingTheory.LocalRing.Module` for
`Module.free_of_flat_of_isLocalRing` and `IsLocalRing.map_mkQ_eq_top`;
`Mathlib.RingTheory.Noetherian.Basic` for `Submodule.FG.of_le`; and
`WeilConjectures.Mathlib.RingTheory.Flat.Equalizer` for
`Module.Flat.of_exact_of_flat_of_flat_right`. `Module.Flat.of_retract` is already available
through the public flatness import. There is no import cycle.

Edge cases checked before finalizing the signature: n = 0 gives the constant polynomial
ring with all nonzero polynomial degrees absent; L = 0 is allowed, is finite and flat, and
has the internal zero grading; a field is allowed as a local ring; negative module degrees
are allowed, with no lower-bound assumption added; unequal positive weights are allowed;
polynomial degrees not attained by any monomial have zero piece; and the coefficient ring
and module have independent universes u and v. The zero coefficient ring is excluded by the
node itself and by `IsLocalRing`. No hypothesis or conclusion was changed and no statement
correction or new node is needed.

Searches performed:

- `msearch.py`, LeanFinder: "A finite graded module over a positively weighted polynomial
  ring over a local ring that is flat over the coefficient ring is finitely presented".
  Eight hits, including `Module.FinitePresentation.of_finite_of_finitePresentation` and
  finite-presentation results for algebras and smooth maps; none states this graded module
  result.
- `msearch.py`, Loogle: "MvPolynomial.weightedHomogeneousSubmodule,
  Module.FinitePresentation". Successful search, zero hits.
- `msearch.py`, grep in Mathlib `RingTheory`: "graded.*[Ff]lat|[Ff]lat.*graded|053C|flat_graded".
  Successful search, zero hits.
- `msearch.py`, LeanSearch: "A finite graded flat module over a polynomial ring over a local
  coefficient ring is finitely presented". Eight hits, all general finite-presentation
  constructors or consequences. `Module.finitePresentation_of_finite` needs a Noetherian
  polynomial ring, not available over the arbitrary local base here;
  `Module.finitePresentation_of_projective` needs projectivity over the polynomial ring.
- `rg` in `WeilConjectures` and `lean/Sheaf` for the item ID, `053C`, `flat_graded`, and both
  orders of graded/flat found no existing theorem. The valuation-module consumer's docstring
  cites the item but does not state it. `dag/lean_names_upstream.json` has no hit for the
  proposed declaration name. Existing project graded-module lemmas are over a field and
  two total-degree variables, not this local coefficient-ring statement.
- `rg` in Mathlib's multivariate polynomial files found
  `Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous`; its definitions were read and the
  existing weighted homogeneous submodule is used directly. `DirectSum.IsInternal` was
  read in `Mathlib.Algebra.DirectSum.Basic` and accepts submodules as well as additive
  subgroups.

No `STATEMENT-DISPUTED` issue was found. The theorem's only postponed proof is its named
`sorry`, with the source and complete natural-language proof in its docstring. Compilation
and the server dry run use only the prescribed wrappers. The maintainer supplies the
independent review; no other worker was started.

## Second reading by Q111

I independently read the immutable item node, all four statement dependency records, the Stacks source place (Tag 053C, `more-algebra.tex` lines 5856--5909), the complete delivered module, and this worker report. The statement is unchanged verbatim. Its hypotheses render a commutative nontrivial local ring (`CommRing` plus `IsLocalRing`), arbitrary `n : ℕ` with positive natural weights, the canonical `MvPolynomial (Fin n) R`, an `R`-module `L` with a `P`-module structure and scalar tower, an internal integer grading by `R`-submodules, graded scalar compatibility, finite generation over `P`, and flatness over `R`. The conclusion is exactly `Module.FinitePresentation P L`; no Noetherian, projective, finite-base, characteristic, or universe-equality assumption is added.

The weighted homogeneous submodule condition is the Mathlib declaration `MvPolynomial.weightedHomogeneousSubmodule`; its weighted support gives the stated degree pieces. Positivity of `hω` yields no negative polynomial degrees, while `DirectSum.IsInternal Ldeg` supplies the internal direct-sum grading. `Module.Finite`, `Module.Flat`, and `Module.FinitePresentation` are the recorded canonical Mathlib notions, with no private duplicate definitions or arbitrary maps. The source and blueprint docstrings are present on the module and theorem. The theorem body is exactly `by sorry`, so it has no hidden local proof; there are no hollow definitions, unbound variables, or route-pivot/pro-etale machinery.

I checked the four proof steps against Tag 053C: homogeneous generators and the degreewise exact sequence; finite free polynomial degree pieces and flat kernel pieces; residue-field reduction, Noetherianity of the polynomial ring over the residue field, and homogeneous relation lifts; and degreewise Nakayama generation of the kernel. The proof references in the node and theorem docstring agree. The direct dependencies are present and their declarations match their recorded interfaces. Independent searches in the project and Mathlib found no existing theorem with this statement, so retaining a new statement node is appropriate.

Edge cases covered by the signature are `n = 0`, the zero module, unattained and negative degrees, unequal positive weights, field coefficient rings, and independent universes `u` and `v`; `IsLocalRing` excludes the zero ring. The route-pivot dropped-node list has no match for this item, and no repair note applies.

Compiler evidence: I ran `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q111 lem-trf-local-graded-flat-module-finite-presentation snapshot/lean/Sheaf/RingTheory/LocalGradedFlatModuleFinitePresentation.lean`. The server side-overlay compile succeeded for both the sandbox and library invocation (exit 0; no errors or warnings beyond the permitted `sorry` status), including the recorded per-file check. No lake/global build, live source write, branch mutation, preflight, claim, merge, or delivery was run.

Finding: the immutable worker report's `## Second reading by Q111` section was only a disclaimer that no second reading occurred. That fails the required real second-reading report gate. The complete replacement report in this `fixes/` directory preserves the worker report and supplies this substantive independent reading. This is a mechanical documentation repair; the mathematics and Lean declaration pass.
