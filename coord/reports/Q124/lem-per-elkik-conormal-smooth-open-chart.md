## Worker report

The module `Sheaf.AlgebraicGeometry.ElkikConormalSmoothOpenChart` states
`AlgebraicGeometry.exists_elkik_conormal_smooth_open_chart`. Its only theorem proof is
`sorry`; there are no new definitions, dependency repairs, or statement corrections.

Sources read: the complete assigned node and all seven statement-dependency records;
the Mathlib declarations listed below; Stacks `smoothing.tex`,
`lemma-improve-presentation` (07CE), lines 342–437; and Elkik II Lemma 3 and Lemma 4,
printed pp.562–565, in https://www.numdam.org/item/10.24033/asens.1258.pdf (online scan).
The scan's additional stabilization variables concern its particular construction;
the assigned existence statement prescribes neither the construction of D nor a value of N.
The statement is rendered unchanged. Its inherited proof is included, step by step,
in the theorem docstring, including its separate zero-localization case.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| R a commutative Noetherian ring | `(R : Type u) [CommRing R] [IsNoetherianRing R]` |
| B a finitely presented commutative R-algebra | `(B : Type u) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]` |
| W an open subscheme of Spec B | `W : (Spec (CommRingCat.of B)).Opens`; its canonical scheme is `W.toScheme`, with inclusion `W.ι` |
| W smooth over Spec R | `hW : Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))` |
| A finitely presented commutative R-algebra D exists | `∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D), Algebra.FinitePresentation R D ∧ ...` |
| R-algebra maps i and r with ri = id | `∃ (i : B →ₐ[R] D) (r : D →ₐ[R] B), r.comp i = AlgHom.id R B ∧ ...` |
| N ≥ c ≥ 0 | `∃ (N c : ℕ), c ≤ N ∧ ...`; natural numbers include zero |
| A surjection p from P = R[x₁,…,x_N], with kernel J | `p : MvPolynomial (Fin N) R →ₐ[R] D`, `Function.Surjective p`; every occurrence of J is `RingHom.ker p.toRingHom` |
| Every h with D_D(p(h)) contained in W_D | `∀ h`, followed by `∀ q : PrimeSpectrum D, p h ∉ q.asIdeal → Spec.map (CommRingCat.ofHom i.toRingHom) q ∈ W`; this is exactly membership in the inverse image defining W_D |
| There exist s and c elements f_j of J | `∃ (s : MvPolynomial (Fin N) R) (f : Fin c → MvPolynomial (Fin N) R)`, with `∀ j, f j ∈ RingHom.ker p.toRingHom` |
| D_D(p(s)) = D_D(p(h)) | Equality of `PrimeSpectrum.basicOpen (p s)` and `PrimeSpectrum.basicOpen (p h)` |
| sJ contained in (f₁,…,f_c) in P | `∀ g ∈ RingHom.ker p.toRingHom, s * g ∈ Ideal.span (Set.range f)` |
| Images of all c by c Jacobian minors generate the unit ideal in D[1/p(s)] | `Ideal.span (Set.range ...) = ⊤`; the range runs over finite subsets S of `Fin N` with `S.card = c`, and its element is the determinant of `(fun j k : Fin c ↦ MvPolynomial.pderiv (S.val.orderEmbOfFin S.property k) (f j))`, mapped by p and then `algebraMap D (Localization.Away (p s))` |
| For c = 0 the sole minor is 1 | The only subset of cardinality zero is empty; its matrix has index `Fin 0`, and `Matrix.det` is the empty determinant 1 |

Taking the determinant in P and then mapping to the localization gives exactly the
images of the minors; it does not ask any single minor to be invertible. The ideal
condition allows their linear combinations. All polynomial variables and universes
are explicitly bound, with `set_option autoImplicit false`. The schemes are in one
arbitrary common universe u, as required by the category `Scheme.{u}`. There is no
size-dependent test-object quantification. The existential D may be taken in this
same universe: finite polynomial constructions and quotients preserve it.

Dependency declarations used, read with their signatures and docstrings:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (196), the abbreviation
  `IsNoetherian R R`, and `isNoetherianRing_iff_ideal_fg` (203).
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` (44),
  the surjective finite-polynomial presentation with finitely generated kernel.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (470), and
  `AlgebraicGeometry.Spec.map` (479). `Mathlib.AlgebraicGeometry.Restrict` (46,52)
  gives `Scheme.Opens.toScheme` and `Scheme.Opens.ι`, available through smooth imports.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` (62),
  the recorded scheme smoothness predicate. Its `HasRingHomProperty` instance is at 73.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (82).
- `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv` (61), the derivation
  giving formal partial derivatives.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det` (60), with the
  Leibniz formula and empty determinant convention.

All already recorded proof modules are imported privately, including
`WeilConjectures.RingTheory.ImprovePresentation`,
`WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation`,
`WeilConjectures.RingTheory.SmoothLocalizationConormalSplit`,
`WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree`, and
`WeilConjectures.LinearAlgebra.Matrix.CauchyBinet`; the Mathlib proof leaves are
imported as well. The proof-only node
`lem-per-symmetric-conormal-free-locus-exact-sequence` currently has neither a Lean
record nor a Mathlib match, so has no module to import. It supplies no notion needed
to type the present statement, and no new theorem for it is introduced here.

Edge cases checked before writing: W may be empty (h then has empty principal open),
D or R may be the zero ring, p(h) may be nilpotent, the localization may be zero,
c and N may both be zero, and c may equal N. For an empty principal open, s=0 and
f=0 satisfy the ideal containment, and in the zero localization the generated ideal
is top. For c=0 the range includes the empty determinant 1. Empty families of f
produce the zero ideal, as required. There is no characteristic assumption or
nontriviality assumption. The binder order makes D,i,r,N,c,p independent of h.
No counterexample or statement fault was found.

Searches actually run:

- `msearch.py ... leanfinder`: “A finitely presented algebra has a retract with a
  fixed polynomial presentation whose kernel has equations with unit Jacobian
  minors on every principal open in a given smooth open”. Eight hits, chiefly
  `Algebra.IsStandardSmooth`, `Algebra.SubmersivePresentation.isStandardSmooth`,
  finite-presentation consequences and the open smooth locus. None gives the
  single fixed retract and presentation over an arbitrary given smooth open.
- `msearch.py ... loogle '"SymmetricAlgebra", "Smooth"'`: successful, zero hits.
- `msearch.py ... grep 'conormal.*smooth|smooth.*conormal|elkik' RingTheory`:
  successful, zero Mathlib hits.
- `rg -n -i 'conormal.*smooth|smooth.*conormal|elkik|lem-per-elkik-conormal-smooth-open-chart'`
  on both project source roots: found related conormal and smooth-presentation
  modules, no exact statement. In particular, read
  `ImprovePresentationSmoothConormalFree.lean`, `ImprovePresentation.lean`, and
  `LocalizedConormalBasisJacobian.lean`: the first assumes global smoothness,
  the second gives a retract with free differentials only over principal opens
  lifted from B, and the third assumes the conormal basis already chosen.
- Exact-id `grep -rn` in `lean/WeilConjectures`: no occurrence.
- Exact proposed declaration-name search in Mathlib, both source roots and
  `dag/lean_names_upstream.json`: no occurrence.

Validation: `scompile.py Q124 lem-per-elkik-conormal-smooth-open-chart <module>`
passed for both sandbox and actual module-name compilation (1.4 seconds each),
with no errors or non-sorry warnings. No global build or direct live edits were made.

## Second reading by Q124

This is a second pass by this worker, not an independent-agent review: the dispatcher
explicitly forbids starting other agents, and the maintainer supplies independent review.
Reread the node against the complete signature. Checked the direction of Spec.map i,
that h ranges over P rather than D, that s is in P, that all f_j are in the exact
kernel of the surjection, and that multiplication containment is in P before any
localization. Checked increasing column order using `orderEmbOfFin`; all subsets of
cardinality c are included. Checked the two successive maps on every determinant
and that the target ideal is in `Localization.Away (p s)`, not in P or D.
Checked c ≤ N, retraction composition order, and the position of every existential
before the universal h. No mismatch was found and no statement change was needed.
