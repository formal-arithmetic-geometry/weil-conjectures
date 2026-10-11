## Worker report

The module `lean/Sheaf/RingTheory/ImprovePresentation.lean` states the existence of the
finite type retract in `Algebra.exists_finiteType_retract_smooth_free_differentials`.
`Algebra.Presentation.symmetricAlgebra_improves` additionally states the node's
parenthetical construction for every finite polynomial presentation. Both proofs are
`sorry`; there are no new definitions, dependency modules, or statement corrections.

Hypotheses and clauses, in order:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- An R-algebra A: `(A : Type v) [CommRing A] [Algebra R A]`.
- Finite presentation: `[Algebra.FinitePresentation R A]` in the existence theorem.
- An A-algebra C: existential binders for C, its commutative ring structure and
  `Algebra A C`. The universe is `max u v`, accommodating the polynomial/conormal
  construction for arbitrary independent universes of R and A. The induced R-algebra
  structure is explicitly the composite of the two algebra maps; it is not independent
  data or a new hypothesis.
- Finite type over A: `Algebra.FiniteType A C`.
- An A-algebra homomorphism ρ: `∃ ρ : C →ₐ[A] A`.
- Retraction: `∀ x : A, ρ (algebraMap A C x) = x`. This explicitly spells out a property
  already inherent in an A-algebra homomorphism to A.
- Every a in A: `∀ a : A` occurs after choosing C and ρ, so the same retract works for
  every a, not a separately chosen algebra for each localization.
- Whenever A_a is smooth over R: `Smooth R (Localization.Away a) → ...`.
- C_a means localization at the image of a: `Localization.Away (algebraMap A C a)`.
- C_a smooth over R: the first conjunct of the consequent is `Smooth R ...`.
- Its Kähler differentials free over C_a: the second conjunct is
  `Module.Free (Localization.Away (algebraMap A C a))
  (KaehlerDifferential R (Localization.Away (algebraMap A C a)))`.
- Parenthetical: for arbitrary `n m : ℕ`, `P : Algebra.Presentation R A (Fin n) (Fin m)`
  supplies precisely the finite polynomial presentation with finitely many relations.
  `P.toExtension.Cotangent` is Mathlib's I/I² with its A-module structure, as read in
  `Mathlib/RingTheory/Extension/Basic.lean` (definition `Cotangent`, line 330, and its
  module instance). The second theorem sets `C := SymmetricAlgebra A
  P.toExtension.Cotangent`. Its named retraction is `SymmetricAlgebra.lift 0`, the
  degree-zero projection, and its conclusion states finite type, retraction, and the
  same simultaneous local smoothness/freeness conditions. Finite presentation of A
  follows from P, so no extra finite-presentation hypothesis is needed there.

Dependency declarations (all four nodes are Mathlib leaves and require no dependency
module):

- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation` and
  `Algebra.Presentation` in `Mathlib.RingTheory.FinitePresentation` and
  `Mathlib.RingTheory.Extension.Presentation.Basic`. Read the class signature, the
  presentation structure and `exists_presentation_fin`.
- `def-weil-pbc-smooth-ring-map`: `Algebra.Smooth` in `Mathlib.RingTheory.Smooth.Basic`.
  Read `FormallySmooth` and `Smooth`: projectivity of Ω, vanishing H1, and finite
  presentation give exactly the node's smoothness predicate.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential` in
  `Mathlib.RingTheory.Kaehler.Basic`, read together with `KaehlerDifferential.D` and
  `KaehlerDifferential.linearMapEquivDerivation`.
- `lem-weil-pbc-symmetric-algebra-universal-property`: `SymmetricAlgebra`,
  `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift`, `lift_ι_apply`, `algHom_ext` in
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`. Read their signatures/docstrings and
  the quotient construction. The second theorem uses `SymmetricAlgebra` and `lift`.

Edge cases checked semantically: zero rings are allowed (no `Nontrivial` binder), a=0
and nilpotent a give zero localization and are not excluded; a=1 tests the global
smooth case. `n=0` and `m=0` are allowed in the explicit construction. There is no field,
Noetherian, characteristic, domain, or positivity hypothesis. Smoothness is genuinely
conditional and is not replaced with an automatically true hypothesis. Freeness is
not strengthened to a specified finite rank. Universe parameters are explicitly bound,
and the existential C can be the symmetric algebra in `Type (max u v)`.

Source read: the statement and entire proof of Stacks Lemma 07CE,
`lemma-improve-presentation`, lines 340–440 of the local Stacks source available at
`/home/ubuntu/c1-stacks-review/smoothing.tex` (the literature path named in the node is
not populated on this machine). Its first clause gives smoothness over A_a in the lci
case; the node uses the smooth case and composition to obtain smoothness over R.
Its second clause gives free differentials and its proof specifies exactly the
symmetric algebra and projection used here. The five proof steps and their dependency
ids are included in the docstrings for stage 3.

Searches for an existing statement (logged by msearch in `searches.jsonl`):

- LeanFinder: “finitely presented algebra admits finite type retract smooth
  localizations with free Kahler differentials”: eight hits including
  `Algebra.smooth_iff`, `Algebra.Smooth`, and `Algebra.Smooth.exists_finiteType`.
  None states the retract or free differentials conclusion; the last is Noetherian
  descent for an already smooth map, not this construction.
- Loogle: `Algebra.Smooth, Module.Free`: no hits.
- Mathlib grep via msearch: `improvePresentation|improve_presentation|SymmetricAlgebra.*Cotangent`:
  no hits.
- LeanSearch: “finitely presented algebra retract symmetric algebra conormal free
  differentials”: service unavailable (Internal Server Error), no conclusion drawn.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf` for the same concept/name patterns: no matching statement; the sole
  `CotangentComplexSymmetricAlgebra.lean` hit concerns the differential sequence of a
  symmetric algebra, not a finite type retract with smooth/free localizations.
- `grep -rn 'lem-weil-pbc-improve-presentation'` in the source repository: no hits.
- `rg` for both chosen full declaration suffixes in Mathlib, source, project Lean and
  `dag/lean_names_upstream.json`: no collisions.

Validation: server single-file compilation succeeded in 1.7 seconds, with no errors or
warnings. No node fault or disputed statement was found. The independent second
reading is left to the assigned second reader.

## Second reading by H1

I independently read the node, both declarations in ImprovePresentation.lean, all
four statement-dependency nodes, and their Mathlib declarations. I read the section
preamble and the entire statement and proof of Stacks 07CE in
`/home/ubuntu/c1-stacks-review/smoothing.tex`, lines 330–440. The section imposes no
standing Noetherian hypothesis: its preceding remark says only that *if* R is
Noetherian, C is finitely presented over R. The node deliberately combines the smooth
case of clause (1), smoothness under composition, and clause (2); it does not claim
the stronger local-complete-intersection conclusion or a free conormal presentation.

Objects, hypotheses, and conclusion clauses matched in order (H3):

1. Commutative base ring R: `(R : Type u) [CommRing R]`. Exact.
2. Commutative R-algebra A: `(A : Type v) [CommRing A] [Algebra R A]`. Exact;
   Stacks' algebras are commutative throughout.
3. A finitely presented over R: `[FinitePresentation R A]`. Exact. Read the class
   in RingTheory/FinitePresentation.lean: a surjective map from a finite polynomial
   ring with finitely generated kernel, as the dependency node specifies.
4. There exists a commutative A-algebra C: `∃ (C : Type (max u v))
   (_ : CommRing C) (_ : Algebra A C)`. Exact. Its R-algebra structure is the
   explicit composite `((algebraMap A C).comp (algebraMap R A)).toAlgebra`.
   This supplies the intended map R → A → C, without independent scalar data.
5. C has finite type over A: `FiniteType A C`. Exact; it does not add finite
   presentation of C or Noetherian assumptions.
6. There exists an A-algebra map rho: `∃ ρ : C →ₐ[A] A`. Exact.
7. Rho retracts the structure map: `∀ x : A, ρ (algebraMap A C x) = x`.
   Exact; this explicitly states the property inherent in this algebra homomorphism.
8. The same C and rho work for every a: `∀ a : A` is inside the existential
   conclusion, after C and rho are chosen. Exact quantifier order.
9. Conditional hypothesis A_a smooth over R: `Smooth R (Localization.Away a) →`.
   Exact. Read Smooth and FormallySmooth in Smooth/Basic.lean: finite presentation,
   vanishing H1 of the canonical cotangent complex, and projective differentials;
   finite generation of differentials follows from finite presentation. No global
   smoothness is assumed.
10. C_a localizes at the image of a: `Localization.Away (algebraMap A C a)`.
    Exact; the induced R action comes from the composite structure map.
11. C_a smooth over R: `Smooth R (Localization.Away (algebraMap A C a))`.
    Exact first conjunct of the conditional conclusion.
12. Omega(C_a/R) free as a C_a-module: `Module.Free
    (Localization.Away (algebraMap A C a))
    (KaehlerDifferential R (Localization.Away (algebraMap A C a)))`.
    Exact second conjunct, without a specified rank. Read KaehlerDifferential,
    its universal derivation D, and linearMapEquivDerivation: these implement the
    precise universal module in def-weil-pbc-kahler-differentials.
13. Parenthetical finite polynomial presentation: the second declaration takes
    `P : Presentation R A (Fin n) (Fin m)`, with arbitrary `n m : ℕ`. Read the
    Presentation structure, its Generators parent, toExtension, quotientEquiv,
    and finitePresentation_of_isFinite. These give a surjective polynomial map
    with exactly the kernel generated by the chosen finite relation family, and
    imply finite presentation without an extra hypothesis. Exact.
14. Specified C = Sym_A(I/I²): `let C := SymmetricAlgebra A P.toExtension.Cotangent`.
    Exact. Extension.Cotangent is the type synonym for the kernel's I/I², with
    the A-module action induced through the quotient; it is not Omega(A/R).
15. Specified rho, projection to degree zero: `SymmetricAlgebra.lift
    (0 : P.toExtension.Cotangent →ₗ[A] A)`. Exact. I read the tensor-algebra
    quotient defining SymmetricAlgebra, its commutative ring instance, lift,
    lift_ι_apply and algHom_ext. The lift kills degree-one generators and fixes A,
    so it is exactly this projection. The second declaration includes finite type,
    retraction, and every conditional smoothness/freeness clause for this specific C.

Edge cases (H3): zero rings R and A are allowed; neither declaration assumes
Nontrivial. The zero algebra and localizations at a = 0 or nilpotent a are covered;
a = 1 recovers the globally smooth case. Both Fin 0 variable and relation families
are permitted: n = 0 and m = 0 are not excluded. Empty schemes are inapplicable to
this ring statement. There is no restriction on characteristic, field structure,
domain structure, or Noetherianity. Independent u and v are bound explicitly;
C in Type (max u v) accommodates the symmetric algebra of the conormal module of a
finite polynomial presentation, so no size case is excluded. No independent universe
of test algebras occurs that could make a hypothesis vacuous.

Independent searches (H4), using different queries from the worker, recorded by
msearch in searches.jsonl:

- LeanFinder: "smooth algebra retract conormal symmetric algebra whose module of
  differentials is free". Eight hits. FormallySmooth.iff_split_injection describes
  splitting the cotangent map for an already smooth algebra; IsStandardSmooth's
  free_kaehlerDifferential requires standard smoothness; retractionKerToTensorEquivSection
  relates infinitesimal sections and linear retractions. None gives this finite type
  enlargement with simultaneous principal-localization conclusions.
- Loogle: `SymmetricAlgebra, Algebra.Smooth`. No hits.
- msearch grep: `retract.*free|free.*retract|symmetricAlgebra_improves`. No hits.
- LeanSearch: "There exists a finite type algebra retract of a finitely presented
  algebra with free Kahler differentials over every smooth principal localization".
  Service unavailable (Internal Server Error); no verdict inferred.
- Independently ran rg over upstream WeilConjectures, project lean/Sheaf, Mathlib
  RingTheory and SymmetricAlgebra for `improv.*present|retract.*smooth|smooth.*retract|
  SymmetricAlgebra.*Cotangent|free.*differential`. The nearby project
  CotangentComplexSymmetricAlgebra module concerns a differential/conormal sequence;
  IndStandardSmooth concerns filtered colimits and cites a different retract lemma
  (07CH). Neither duplicates this statement. The Mathlib standard smooth hits assume
  a stronger hypothesis and do not construct C. No existing exact statement found.
- rg for both declaration names and the blueprint id in upstream Lean and
  dag/lean_names_upstream.json found no collisions.

No new nodes or dependency modules are in this delivery, and all four dependencies
have usable Mathlib records. No statement correction was needed (H7); no citer review
is required. Both docstrings contain the source tag, blueprint id, and all five proof
steps with their dependency ids (H8). There are two named theorems with sorry proofs,
no new definitions or instances, no hollow data, and no proved theorem (H5/H6).
Imports each supply a used notion; namespaces, header, bound universes and variables,
and line lengths follow the conventions (H9).

Mismatch repaired (H2): the worker's node lean.statement had normalized spaces rather
than the signature verbatim. I replaced only that metadata value with the exact
multiline primary signature, from `theorem` through the result type before `:= by`.
The Lean source and the mathematical node statement needed no changes.

Validation: the prescribed scompile single-file check passed in 1.6 seconds with
exit code 0, no errors, and no warnings. I also checked the signature text against
the node record and all Lean lines against the 100-character convention.
