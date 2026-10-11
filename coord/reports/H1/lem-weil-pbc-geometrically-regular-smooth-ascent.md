## Worker report

The module `Sheaf.RingTheory.GeometricallyRegularSmoothAscent` states
`Algebra.isGeometricallyRegular_of_smooth`. It introduces a field `k`, commutative rings
`A` and `B`, `k`-algebra structures, an `A`-algebra homomorphism
`φ : A →ₐ[k] B`, smoothness of the induced `A`-algebra structure, Noetherianity of `A`,
and geometric regularity of `A`; its conclusion is Noetherianity of `B` together with
geometric regularity of `B`.

The Lean rendering of each hypothesis is:

* “k is a field” is `[Field k]`.
* “A and B are commutative rings” is `[CommRing A] [CommRing B]`.
* “A and B are k-algebras” is `[Algebra k A] [Algebra k B]`.
* “φ is a homomorphism of k-algebras” is `(φ : A →ₐ[k] B)`.
* “φ is smooth as an A-algebra map” is `hsmooth`, whose proposition installs
  `φ.toRingHom.toAlgebra` and asserts `Algebra.Smooth A B`.
* “A is Noetherian” is `(hnoetherian : IsNoetherianRing A)`.
* “A is geometrically regular over k” is
  `(hregular : IsGeometricallyRegular k A)`, the declaration from
  `Sheaf.RingTheory.GRing`.

The conclusion `B is Noetherian and geometrically regular over k` is rendered as
`IsNoetherianRing B ∧ IsGeometricallyRegular k B`. The proof is `sorry`, as required
for stage 2. The proof docstring follows the source proof: finite-presentation ascent of
Noetherianity, purely inseparable base change, smooth base change, regularity ascent,
and the geometric-regularity definition.

Dependencies used are `Sheaf.RingTheory.GRing`, declaration
`Algebra.IsGeometricallyRegular`, and Mathlib's `Mathlib.RingTheory.Smooth.Basic`
(`Algebra.Smooth`). The node `def-weil-pbc-noetherian-ring` is Mathlib's
`IsNoetherianRing`; it is used directly in the hypotheses and conclusion.

Edge cases checked: `k'` in geometric regularity is quantified by the dependency's
`Type (max u v)` convention, so the statement does not exclude finite purely inseparable
extensions; no nonzero, finite, or characteristic assumptions were added, and the
Noetherian conclusion is retained even for arbitrary smooth maps in the stated universes.

Searches for an existing declaration: `msearch.py ... leanfinder` for “A smooth algebra
over a geometrically regular algebra over a field is geometrically regular” returned only
`Algebra.Smooth` and unrelated standard-smooth declarations; `msearch.py ... loogle`
for `Algebra.Smooth, IsRegularRing` returned no hits; `msearch.py ... leansearch`
for “smooth map preserves geometric regularity of algebras over a field” was unavailable;
`msearch.py ... grep` for `geometrically.?regular|IsGeometricallyRegular|IsRegularRing.*Smooth`
found no ascent theorem. `rg` in the source and Sheaf trees found only the existing
geometric-regularity definition and downstream uses, including no declaration with this
item's statement. Thus no existing declaration was recorded.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by H1

I read the sandbox node and module, all three statement dependency nodes, and the
declarations they record. The literature directory in this clone has no Stacks checkout;
I read the local Stacks source at `/home/ubuntu/c1-stacks-review/algebra.tex` instead,
whose tag table confirms 07QF, 0381, 0382, 00T2, 07NF, and 00FN. In particular,
lines 47090–47200 give the section assumptions, the geometric regularity definition,
and the ascent lemma and proof. The source assumes a field and Noetherian algebras,
not finite type over the field or a perfect field. Smoothness supplies finite
presentation over A and hence Noetherianity of B by 00FN.

Object, hypothesis, and conclusion checklist:

* Field k: `{k : Type u} [Field k]`. Exact; all characteristics are allowed.
* Commutative rings A and B: `{A : Type v} {B : Type w}` and
  `[CommRing A] [CommRing B]`. Exact; no domain or nonzero assumption.
* Their k-algebra structures: `[Algebra k A] [Algebra k B]`. Exact;
  neither algebra is assumed finite over k.
* The k-algebra homomorphism φ: `(φ : A →ₐ[k] B)`. Exact; its algebra
  homomorphism law is precisely the required compatibility with k.
* Smoothness of this map: `hsmooth` installs `φ.toRingHom.toAlgebra` and asserts
  `Algebra.Smooth A B`. Exact; this is smoothness of φ rather than smoothness for
  an independently chosen A-algebra structure. I opened Smooth/Basic.lean:
  `Smooth` has formal smoothness and finite presentation; `FormallySmooth` has
  projective differentials and vanishing H1. This is the recorded Mathlib match
  for def-weil-pbc-smooth-ring-map and Stacks 00T2. Finite presentation makes
  the differentials finite; no additional hypothesis is introduced here.
* A Noetherian: `(hnoetherian : IsNoetherianRing A)`. Exact; the recorded
  Noetherian/Defs abbreviation means every ideal is finitely generated.
* A geometrically regular over k: `(hregular : IsGeometricallyRegular k A)`.
  Exact. The dependency's recorded declarations explicitly include
  `Algebra.IsGeometricallyRegular`; I opened GRing.lean, where it is Noetherianity
  together with regularity of `TensorProduct k k' A` for every finite purely
  inseparable field extension k'/k. This is condition (2) of 0381, used by 0382.
  `IsRegularRing` in Mathlib includes Noetherianity and regular local rings at
  every prime, so the ring regularity clause also agrees. The separate
  Noetherian hypothesis repeats a clause of this definition, as the node does.
* B Noetherian: the first conjunct `IsNoetherianRing B`. Exact, retained explicitly.
* B geometrically regular over the same k and the given k-algebra structure:
  the second conjunct `IsGeometricallyRegular k B`. Exact. No existentially
  chosen structure or weaker conclusion replaces it.

Edge cases: arbitrary independent universes u, v, w are bound. The dependency
quantifies over extension fields in `Type (max u v)` for A and `Type (max u w)`
for B. Finite extensions of k admit representatives at these levels, so neither
test quantifier is vacuous and universe transport covers the same extensions.
Zero rings A or B are not excluded; in particular B = 0 remains permitted,
and if A = 0 the existence of φ forces B = 0. The corresponding empty spectra
therefore remain included. Empty presentations and relative dimension zero are
not excluded by `Smooth`; there is no explicit index set or n in this statement.
No characteristic restriction occurs; the trivial extension is included even
in characteristic zero. There is no hidden local, reduced, perfect, or finite
dimensional instance in the signature.

Independent searches used different queries from the first worker:

* LeanFinder: “Geometric regularity is preserved by a smooth homomorphism of
  algebras” returned eight smooth-ring-map and standard-smooth declarations,
  including `RingHom.Smooth.toAlgebra`; none states geometric regularity ascent.
* Loogle: `Algebra.Smooth, IsNoetherianRing` returned only
  `Algebra.Smooth.flat_of_isNoetherianRing`, whose conclusion is flatness.
* LeanSearch: “Base change by finite inseparable fields of a smooth algebra over
  a geometrically regular ring is regular” was unavailable (HTTP internal error);
  this is recorded as unavailable, without a mathematical verdict.
* msearch grep: `IsGeometricallyRegular|geometric.{0,15}regular|IsRegularRing.*[Ss]mooth|[Ss]mooth.*IsRegularRing`
  returned no Mathlib match. Direct rg searches of Mathlib, the source's
  WeilConjectures tree, the project's Sheaf tree, and dag/lean_names_upstream.json
  found the project's GRing definition and downstream uses, but no ascent theorem
  with this signature. Source theorems about regular schemes smooth over a field
  have different objects and hypotheses. No duplicate definition or theorem is needed.

No new nodes, dependency modules, or statement correction are present or needed.
The five proof-docstring steps match the node's five steps, including the
tensor-product identification and named dependencies. The module and theorem
docstrings name 07QF and the exact blueprint id; both imports are used. The only
proof is the required `sorry`, and there are no definitions or hollow data.
The recorded `lean.statement` is verbatim the file's signature, with all variables
and universes bound. No mismatch was found, so the Lean and node were kept unchanged;
the second reading added only this review and the independent search evidence.
The server single-file compile succeeded in 1.5 seconds with no warnings or errors.
