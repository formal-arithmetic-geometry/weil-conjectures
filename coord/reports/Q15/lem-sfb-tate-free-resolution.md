## Worker report

The module `Sheaf.RingTheory.TateFreeResolution` states
`GradedAlgebra.exists_tate_free_resolution`, with its sole proof `by sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.
The source is the local Stacks `literature/stacks-project/dpa.tex`, Tag 09PN,
`lemma-tate-resolution`, including its finite-generator assertion and construction
(lines 1207--1299). The node's finite prescribed-presentation specialization agrees
with that source. The declaration docstring includes all six proof steps of the node.

Hypothesis and clause correspondence:

- Commutative Noetherian R: `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- Commutative R-algebra S: `(S : Type v) [CommRing S] [Algebra R S]`.
  These universes are independent; the witness algebra uses `Type (max u v)`.
- The prescribed finite polynomial presentation, including n = 0:
  `(n : ℕ) (π : MvPolynomial (Fin n) R →ₐ[R] S)` and
  `(hπ : Function.Surjective π)`.
- A nonnegative strictly commutative graded R-algebra and its compatible divided
  powers/differential: `A : VariableAdjunction.AlgebraData R` and
  `D : DividedPowerDGA A.grade`. These are the recorded dependency structures,
  not replacement definitions. `AlgebraData` bundles its ring, R-algebra, grading,
  and strict graded commutativity instances.
- A_0 = P: `ι : MvPolynomial (Fin n) R →ₐ[R] A.Carrier`,
  `Function.Injective ι`, and the equivalence
  `x ∈ A.grade 0 ↔ ∃ f, ι f = x`. This expresses the equality of algebras up to
  the specified identification inside the total graded algebra. It retains the
  full polynomial algebra even when the augmentation has a nonzero kernel.
- The augmentation is `ε : A.Carrier →ₐ[R] S`.
  Its degree-zero part is exactly π by `ε.comp ι = π`.
  Concentration of S in degree zero is rendered by the vanishing of ε on every
  positive homogeneous component. Being a chain map is `∀ x, ε (D.d x) = 0`.
  The degree and multiplication conditions make this a map of graded algebras;
  preservation of positive divided powers follows since their positive-degree
  values map to zero, while the zeroth divided power maps to one.
- H_0(A) is S **via ε**: `∃ h : D.homology 0 ≃ₗ[R] S`, with
  `h (D.chainComplex.homologyπ 0 z)` equal to ε evaluated on the actual cycle
  inclusion `D.chainComplex.iCycles 0 z` for every cycle z. `Subtype.val (@id …)`
  merely exposes that included cycle as an element of the total algebra.
  Thus the equivalence is augmentation-induced, rather than an arbitrary module
  equivalence. Since ε is an algebra map, this equivalently gives its usual
  ring/algebra homology identification without adding a second homology definition.
- H_i(A) = 0 for every i > 0:
  `∀ i : ℕ, 0 < i → Subsingleton (D.homology (i : ℤ))`.
  These are the recorded Mathlib homology objects of D's actual differential.
- The underlying graded divided-power algebra is polynomial, starting with P,
  with finitely many variables in each positive degree: the final existential
  witnesses B, γ, b, J, p, and q expand/refine the dependency's `IsPolynomial`
  presentation. `b : MvPolynomial (Fin n) R ≃ₐ[R] (B 0).Carrier` and the grade
  condition put P in degree zero. `Finite (J k)` and
  `SetPresentation (B k) (γ k) (k + 1) (J k) (B (k + 1))` adjoin only a finite
  set of variables in degree k+1. `SetPresentation` carries the actual iterated
  exterior/divided-symbol module coordinates and multiplication, not just abstract
  finite generation. `SetNormalized` gives the extended divided powers.
  `UnionPresentation` specifies injective compatible graded inclusions and coverage.
  `(q.into 0).toAlgHom.comp b.toAlgHom = ι` fixes the initial polynomial map;
  `Preserves (q.into k) (γ k) D.toGradedDividedPowers` fixes all divided powers.
  Degree k+1 is the source construction's order and covers each positive degree
  once; empty sets permit stages without new generators.
- Each A_i is R-free: `∀ i : ℕ, Module.Free R (A.grade i)`.
- The augmented free resolution consequence: exactness at A_0 is explicitly
  `Function.Exact (D.componentDifferential 0).hom
  (ε.toLinearMap.domRestrict (integerComponent A.grade 0))`.
  The second map is the restriction ε_0, identified with π above. Surjectivity
  onto S follows from the given hπ and this identification. Exactness at every
  positive degree is exactly the preceding vanishing of D's homology; freeness
  is the preceding Module.Free assertion. No extra acyclicity hypothesis is used.

Dependency declarations read and used:

- `Sheaf.RingTheory.DividedPowerDGA`: `GradedAlgebra.DividedPowerDGA`,
  `componentDifferential`, `chainComplex`, `homology`, and the full `IsPolynomial`
  signature/docstring. The differential/chain complex/homology in the theorem are
  these exact constructions.
- Through that module, `Sheaf.RingTheory.DividedPowerVariableAdjunction`:
  `VariableAdjunction.AlgebraData`, `SetPresentation`, `SetNormalized`,
  `UnionPresentation`, and `Preserves`; their signatures and constituent finite
  tower descriptions were read. These are also the stated proof dependency
  `lem-sfb-divided-power-variable-adjunction`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; its docstring and
  `isNoetherianRing_iff_ideal_fg` give precisely finite generation of every ideal.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; also read the recorded
  `algHom_ext`, and `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` supplies the standard
  R-module freeness assertion.
- Plain proof imports: `Mathlib.RingTheory.FiniteType` for the recorded
  `Algebra.FiniteType.isNoetherianRing`, and `Mathlib.RingTheory.Noetherian.Basic`
  for `Submodule.FG.of_le`. Both source signatures were read. The proof dependency
  `lem-sfb-adjoin-dga-cycle` has no recorded module in this checkout, so no import
  can yet be written; its use is retained in the proof docstring and unchanged DAG.

Edge cases checked before writing: n = 0 means the ordinary polynomial ring on
`Fin 0`; no positive lower bound on n appears. The zero ring and zero algebra are
allowed; no Nontrivial or characteristic restriction is imposed. Zero kernels and
zero higher homology permit empty variable sets, including all later sets empty.
Odd variables use the strict square-zero interface, valid in characteristic two.
Unboundedly many nonempty degrees are permitted. The witness universe dominates
both R and S, and the linear homology equivalence allows their independent sizes.
The finite-generator conclusion is not changed into finite freeness over R: R-free
components may have an infinite ordinary-polynomial monomial basis.

Searches performed on 2026-10-24:

- `msearch.py … leanfinder "Tate resolution with prescribed polynomial degree zero
  and finite divided power variables in every positive degree"`: eight hits,
  including ordinary `dividedPowersBot` constructions and projective resolutions;
  none states this DGA theorem.
- `msearch.py … loogle '"Tate", "resolution"'`: five unrelated Lean structure
  elaboration-state hits, no mathematical resolution theorem.
- `msearch.py … leansearch "A finite type algebra over a Noetherian ring admits a
  Tate divided power free differential graded resolution with prescribed polynomial
  augmentation"`: eight finite-type/finite-presentation/Noetherian results, no
  matching resolution.
- `msearch.py … grep 'Tate.?[Rr]esolution|tate_resolution|divided.?power.*resolution'`:
  zero Mathlib hits.
- `rg` with that pattern over `lean/WeilConjectures` and `lean/Sheaf`: supporting
  docstring references in the graded-algebra modules and the self-Tor/conormal
  comparison modules, no theorem giving the present resolution. The upstream
  `SelfTorConormalComparisonTateConstruction.lean` was opened: its theorem concerns
  comparison maps for exterior powers and Tor, not the present existence statement.
- `grep -rn 'lem-sfb-tate-free-resolution' lean/WeilConjectures`: no hits.
- Exact name searches for `exists_tate_free_resolution|TateFreeResolution` over
  Mathlib, both source roots and `dag/lean_names_upstream.json`: no collision.

Validation: the final file compiled through the prescribed `scompile.py` wrapper
both as a sandbox module and as `Sheaf.RingTheory.TateFreeResolution`, with no
errors or warnings. No local Lean command or global build was run.

## Second reading by Q15

The dispatch brief requires a single worker and prohibits starting other agents;
this is an explicit worker reread, not a claim of an independent second worker.
The maintainer's independent review follows delivery. I reopened the node and
reread the complete final signature against each clause above.

The augmentation is fixed on the whole P, not merely on generators or as some
surjection. The image-equals-grade-zero and injectivity clauses retain A_0=P.
The homology equivalence is constrained on every cycle class and therefore is the
one induced by ε. In particular, a module with isomorphic homology but a wrong
augmentation cannot satisfy the statement. The finite sets J belong to the actual
normalized polynomial tower, whose zero-stage inclusion is required to equal ι;
an unrelated polynomial presentation cannot witness the conclusion. All positive
degrees and characteristic two remain covered, and no nonzero ring assumption
was introduced. The explicit exactness clause uses the same D and ε.

The first compiler pass found a coercion issue in the cycle-value expression;
`Subtype.val (@id (integerComponent A.grade 0) …)` resolved it without changing
its mathematical content. The final reread found no statement mismatch. The node
copy changes only `lean`. No statement dispute or source correction is needed.
