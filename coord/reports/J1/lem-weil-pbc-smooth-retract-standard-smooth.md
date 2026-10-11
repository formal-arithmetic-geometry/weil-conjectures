## Worker report

The module `Sheaf.RingTheory.SmoothStandardSmoothRetract` states
`Algebra.Smooth.exists_standardSmooth_retract`. It introduces commutative rings `R` and `A`,
an `R`-algebra structure on `A`, and `[Smooth R A]`. Its conclusion quantifies a ring `B` in
`Type (max u v)`, a commutative-ring structure and an `R`-algebra structure on `B`; requires
`Algebra.IsStandardSmooth R B`; and supplies `R`-algebra maps `ι : A →ₐ[R] B` and
`ρ : B →ₐ[R] A` with `ρ.comp ι = AlgHom.id R A`. The final conjunct is smoothness of
`A → B` using the algebra structure induced by `ι`, rendered explicitly as
`@Smooth A _ B _ ι.toRingHom.toAlgebra`.

The theorem proof is `sorry`, as required for stage 2. The docstring records all fourteen
proof steps from the node, including the relative complete-intersection construction, split
conormal sequence, polynomial extension and retraction, localization, fibre and miracle
flatness arguments, the etale square presentation, and the final standard-smooth presentation.

Dependency declarations used: `Algebra.Smooth` from `Mathlib.RingTheory.Smooth.Basic` (the
node `def-weil-pbc-smooth-ring-map`); and `Algebra.IsStandardSmooth` from
`Mathlib.RingTheory.Smooth.StandardSmooth` (the node `def-weil-pbc-standard-smooth`). No
private copies of these notions were introduced.

Edge cases checked: the existential `B` uses `Type (max u v)` so it permits either ring's
universe; `n,c` in the source presentation may be zero; the source proof explicitly handles
the zero algebra in its square-presentation step; and no nonemptiness, field, or
Noetherian hypothesis was added. The algebra-map smoothness clause uses the given `ι`, rather
than an unrelated algebra structure.

Searches for an existing declaration:

* `msearch.py ... leanfinder "smooth algebra is a retract of a standard smooth algebra with smooth inclusion"` found smoothness and formal-smoothness declarations but no retract theorem.
* `msearch.py ... loogle "Algebra.Smooth, Algebra.IsStandardSmooth"` found only standard-smooth/localization results, not this statement.
* `msearch.py ... grep "retract|retraction" RingTheory/Smooth` found general retraction lemmas for different notions, with no matching smooth-algebra theorem.
* `rg` over `WeilConjectures` and `lean/Sheaf/RingTheory` found no declaration for this node (only downstream references and unrelated retractions).
* The Stacks source for Tag 07CH confirms the exact conclusion: a smooth `R`-algebra map `A → B` with retraction and `B` standard smooth over `R`.

The server compiler completed this module with no errors or warnings (the expected `sorry`
warning is suppressed by the project settings).

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the dry-run tool accepts the report without this
section and will request it during review.

## Second reading by J1

I independently read the sandbox node and full Lean module, both statement dependency
nodes, Mathlib's `Smooth` and `FormallySmooth` declarations, `IsStandardSmooth.out`, and
`PreSubmersivePresentation`/`SubmersivePresentation`. The Stacks source is absent in this
machine's literature checkout, so I read the server's `literature/stacks-project/smoothing.tex`
by read-only ssh: the introduction and Lemma `lemma-smooth-standard-smooth` with its full
proof (Tag 07CH). The lemma has no standing Noetherian, field, or characteristic assumption;
the introduction's Noetherian assumption concerns Popescu's main theorem, not this lemma.

Object/hypothesis/conclusion inventory, matched item by item:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary commutative base ring R | `(R : Type u) [CommRing R]` | Exact. |
| Commutative R-algebra A | `(A : Type v) [CommRing A] [Algebra R A]` | Exact; no extra property of R or A. |
| A smooth over R | `[Smooth R A]` | Exact dependency notion: formal smoothness plus finite presentation; formal smoothness is projective differentials and vanishing H1Cotangent. Finite presentation makes the differentials finite. |
| Existence of a commutative R-algebra B | `∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B)` | Exact; existential structures, no extra assumptions. |
| B standard smooth over R, equivalently the finite quotient presentation with a unit Jacobian minor | `IsStandardSmooth R B` | Exact Mathlib match of def-weil-pbc-standard-smooth-algebra. Its finite submersive presentation includes injective relation-to-variable selection and a unit Jacobian. Reordering finite variables places the selected variables first; conversely the node's first-c-variable presentation gives that injection. No presentation clause is lost. |
| R-algebra inclusion iota and R-algebra retraction rho | `∃ (ι : A →ₐ[R] B) (ρ : B →ₐ[R] A)` | Exact, maps respect the same R-algebra structures. Injectivity follows from the retraction and need not be added. |
| rho composed with iota is the identity on A | `ρ.comp ι = AlgHom.id R A` | Exact direction and equality of algebra maps. |
| B smooth as an A-algebra via this iota | `@Smooth A _ B _ ι.toRingHom.toAlgebra` | Exact; explicitly fixes the algebra structure to this map, with no unrelated A-action or additional tower assumption. |

Quantifiers are in the node's order: R and its algebra A with smoothness, then B with
structures and standard smoothness, then the two maps and their retraction/smoothness
properties. The placement of standard smoothness before the map existential is equivalent
to the node's conjunction because it does not depend on either map.

Edge cases: neither ring is required nontrivial, so the zero base/algebra and the corresponding
empty spectra are included. Mathlib supplies standard smoothness for subsingleton algebras;
the node's proof step 13 explicitly handles B = 0. Empty finite relation/variable sets,
c = 0 and n = 0 are permitted by the finite presentation definition (empty determinant 1).
There is no characteristic restriction. Universes u and v are separately declared and bound;
a polynomial quotient/localization construction over R and A fits in `Type (max u v)`.
Finite index types in `IsStandardSmooth` may be reindexed by `Fin`, so its `Type` index
binders do not impose a mathematical universe restriction. No test-object quantifier occurs.

Independent searches used different wording from the worker:

- LeanSearch: "Every smooth commutative algebra is an algebra retract of an algebra admitting
  a submersive presentation". The service returned Internal Server Error; unavailable,
  recorded in searches.jsonl, and no negative verdict inferred from it.
- Loogle: `"IsStandardSmooth", "comp"`. Five hits, all composition stability of standard
  smooth maps; none states this retract theorem.
- LeanFinder: "A smooth algebra embeds by a smooth homomorphism into a submersively presented
  algebra and admits an algebra section back". Eight hits: smoothness definitions,
  submersive-presentation standard smoothness, and standard-smooth implies smooth; no retract.
- Logged Mathlib grep: `Smooth.*(retract|section)|IsStandardSmooth.*(exists|retract)|07CH`
  in RingTheory. Hits concern cotangent sections, Noetherian descent, or an etale polynomial
  presentation for an already standard smooth algebra; none is this existence statement.
- Independent rg in all source WeilConjectures and project lean/Sheaf for Tag 07CH,
  the declaration name, and smooth/standard/retract combinations found downstream docstring
  references only. Broader retract/retraction searches in RingTheory found conormal-section
  correspondences, completion flatness, and unrelated weaker presentation-improvement
  statements. These do not replace this theorem.

Mismatch found: the Worker report names `def-weil-pbc-standard-smooth` as the dependency,
whereas the node actually cites `def-weil-pbc-standard-smooth-algebra`. The latter's recorded
Mathlib match is `Algebra.IsStandardSmooth` and is exactly the notion used here. This section
corrects that report reference; the Worker report is preserved. No mathematical or Lean
mismatch was found, so the module and node record were left unchanged. There are no new
nodes, dependency modules, or statement corrections in this delivery.

The module has only one theorem, with proof `sorry`, and no definition, local instance,
private notion, or file-local notation. Both docstrings give Stacks 07CH and the item's
blueprint tag. I checked all fourteen proof steps against the node: the docstring includes
the complete-intersection retract, conormal splitting, polynomial extension, differential
annihilation, localization, smooth retraction, fibre ranks, regular local dimensions,
zero-dimensional fibres, miracle flatness, fibre criterion, etaleness, square presentation,
and final standard-smooth conclusion. Both imports serve the statement. The stored
lean.statement is verbatim the signature, all variables/universes are bound, and lines obey
the 100-character limit. Server single-file compilation is checked before delivery.
