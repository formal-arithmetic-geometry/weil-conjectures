## Worker report

States `AlgebraicGeometry.parameterRoot_punctured_cover_tower` in
`Sheaf.AlgebraicGeometry.ParameterRootPuncturedCoverTower`. The sole postponed
proof is this named theorem. Its docstring gives all eleven reviewed DAG proof
steps and their sources. Four ancillary declarations have real data:
`ParameterRootTower.puncturedLevel`, `puncturedFull`, `levelMap`, and `fullMap`.
The first two abbreviate the indicated localizations of literal quotient rings;
the latter two are `IsLocalization.Away.map` of their structural ring maps.
No definition chooses data from the postponed theorem.

The prior worker's quoted rejection concerned an already accepted stage-1 split.
At the original submission the node had no Lean record and the queue listed it
at stage 2. Q47's acceptance and all other nonowned metadata are preserved.
The current sandbox initially contained only dispatcher brief markers. No prior
Lean delivery, report, or node packet was available to repair.

Hypotheses and objects, matched individually:

- A positive prime p: `(p : ℕ) (hp : p.Prime)`; primality includes positivity.
- An arbitrary commutative characteristic-p coefficient ring: `(H : Type u)
  [CommRing H] [CharP H p]`. There is no Noetherian, reducedness, locality,
  henselianity, or regularity assumption. Finite-root quotients are written
  directly with the polynomial and quotient APIs.
- A possibly empty parameter list: `(r : ℕ) (t : Fin r → H)`. There is no
  injectivity or nonzero-parameter hypothesis. The denominator is always
  `∏ i, t i`, with the empty product equal to one.
- The index N_p is the existing `ProEtale.TameRootOrder p`, literally
  `{n : ℕ // 0 < n ∧ n.Coprime p}`. Every compatibility quantifies over
  `n.val ∣ m.val`, not over the usual order on the natural numbers.
- H_n is the literal quotient `MvPolynomial (Fin r) H ⧸ Ideal.span
  (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))`.
  It uses the already-cited polynomial and quotient definition nodes directly.
- H_infinity is the existing `ProEtale.tameRootAlgebra p t`. Its real presentation
  has variables `(i,n)` and both root and divisibility relations. The theorem
  asserts its colimit universal property; it does not assume it or replace the
  colimit by an arbitrary ring admitting roots.

Conclusions, matched individually and in signature order:

1. The existential `transition` consists of H-algebra maps, so coefficients
   are fixed as part of `AlgHom`. The first conjunct specifies each image
   `transition n m h (class X_i) = (class X_i)^(m.val/n.val)`. These equations
   determine the maps uniquely by polynomial and quotient universal properties.
2. `transition n n (dvd_refl _) = AlgHom.id H _` is the identity law;
   `(transition m l h').comp (transition n m h) = transition n l (h.trans h')`
   is the composition law. No category ordered by the ordinary size of n is used.
3. The level basis is an existential `Module.Basis (Fin r → Fin n.val) H H_n`
   whose value at e is exactly `∏ i, (class X_i)^((e i).val)`. Its finite index
   set has cardinality n^r; thus it states the specified basis, finite freeness,
   and the claimed rank together, including the zero coefficient ring case
   whenever the corresponding ring instance exists.
4. For n dividing m, the `RingEquiv` has source the SAME existing finite-root
   construction, now over H_n with parameters `class X_i` and exponent m/n.
   Its coefficient equation `e (algebraMap _ _ a) = transition n m h a` makes
   it an isomorphism over H_n; its generator equation sends the new y_i to
   the mth-root coordinate. This is exactly the displayed transition presentation.
5. The second `Module.Basis` is indexed by `Fin r → Fin (m.val/n.val)` and has
   the same prescribed monomial values in H_m. Its scalar action is explicitly
   `@Algebra.toModule ... (transition n m h).toRingHom.toAlgebra`, so it is a
   basis over H_n via the actual transition, with rank (m/n)^r. No ambient
   or unspecified scalar action is substituted.
6. `inclusion` consists of H-algebra maps to the full compatible-root quotient.
   The formula sends class X_i at order n to class X_(i,n). The next conjunct
   gives compatibility with every transition.
7. The first `∃!` clause against every commutative `Q : Type u` gives the
   unlocalized ring-colimit universal property with EXACTLY these inclusions.
   It includes maps not presented as H-algebra maps, so this is a colimit
   in commutative rings as stated in the node.
8. `localizedTransition` is specified by its value on every image of H_n
   under the localization map. The target is the literal localization of H_m
   at the image of the original f. Inverses are forced by the ring-hom laws;
   thus these are the canonical localized maps, not arbitrary witnesses.
9. For each n, `RingHom.FaithfullyFlat (levelMap t n.val)` and the three
   `IsFinite`, `Etale`, and `Surjective` assertions refer to the SAME localized
   structural map. `levelMap` is its explicit localization construction.
10. For each n dividing m, those same four properties are asserted for
    `localizedTransition n m h`. This includes every transition, not only
    the maps out of level one or transitions between consecutive powers.
11. `localizedInclusion` has its value specified on every image of H_n;
    the next equations make it compatible with the localized transitions
    and identify its composite with each `levelMap` as the explicit `fullMap`.
12. The second ring `∃!` clause asserts that the localization of the REAL full
    quotient is the colimit of the localized finite levels, with the specified
    level maps. Together with clause 7, this is exactly
    H_infinity[1/f] = colim H_n[1/f] up to its canonical compatible isomorphism.
    No arbitrary isomorphism or unrelated identification is used.
13. The `∀ (Z : Scheme.{u})` unique-factorization clause is the inverse-limit
    universal property of the spectrum of this ring with projections
    `Spec.map (localizedInclusion n)`. It tests EVERY scheme, not only affine
    schemes or topological spaces, and uses the same compatibility equations.
    All levels and the vertex are literal spectra and hence affine. The
    preceding coefficient equation also identifies the map to Spec H[1/f].
14. The full structural map is faithfully flat and surjective on spectra.
    `Presieve.singleton (Spec.map (CommRingCat.ofHom (fullMap p t))) ∈
    Scheme.proetalePrecoverage ...` states that the actual limit map is a
    singleton pro-etale covering. The precoverage includes weak etaleness
    AND its fpqc covering condition; this is stronger information than
    merely saying the source is an object of the pro-etale site, exactly as
    the node requires. The faithful-flat conclusion is also explicit in
    step 9 of the existing node proof.
15. `Function.Bijective (algebraMap H (MvPolynomial (Fin r) H ⧸
    Ideal.span (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ 1 -
    MvPolynomial.C (t i)))))` gives the canonical identity-level identification for n=1. For r=0,
    the last implication gives bijectivity of the structural maps to every
    finite level and the full quotient. With the displayed coefficient and
    transition equations these identify every map as the identity on H.
    For m=n the transition is literally `AlgHom.id`. It does not assert that
    H_1 to H_m is an identity for arbitrary m: that false interpretation
    of the node's last sentence was already excluded by Q47's accepted report.

Dependencies and exact declarations read and reused:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`. The node's recorded
  declarations were read in full with their docstrings.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic`: `IsLocalization.Away`,
  `IsLocalization.Away.map`. This is the recorded localization notion,
  with the ring structure and map supplied by its ring-localization module.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` (recorded small
  site) and `Scheme.proetalePrecoverage` (the exact singleton covering notion).
  No replacement pro-etale definition is introduced.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`;
  the colimit is rendered by its universal property rather than by a second
  chosen object. The spectrum limit is similarly rendered by its universal property.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`, the
  latter using the algebra structure induced by the named ring homomorphism.
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`;
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`, and `Ideal.Quotient.liftₐ`. These give the recorded
  quotient and algebra-map interface; `Ideal.Quotient.mk` denotes its root classes.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`;
  `Mathlib.LinearAlgebra.Basis.Defs`: `Module.Basis`. The explicit finite
  monomial bases provide the claimed freeness and numerical ranks.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- The finite-root quotient now uses only the already-cited definition nodes
  `def-weil-pbc-mv-polynomial-ring` and `def-weil-pbc-algebra-hom-quotient`.
  There is no import or statement dependency on the strict-local splitting theorem.
- Gained already-landed dependency `def-sfb-strict-local-kummer-tame-module`,
  module `Sheaf.Paper.StrictLocalKummerTameModule`:
  `ProEtale.TameRootOrder`, `tameRootRelations`, `tameRootAlgebra`. This gained
  dependency was checked in the original submission by traversing its full
  statement/proof dependency closure: it does not reach this item.

Proof-only modules are imported plainly for unit-binomial finite etaleness,
faithful flatness of directed colimits, ind-etale comparison and its universe
transport, the monic quotient power basis, spectrum/colimit-limit comparison,
faithfully-flat spectrum surjectivity, tensor products, composition of covers,
and affineness. No missing dependency interface required repair. No new node
or dependency-node file is delivered.

Edge cases checked before the statement was written:

- r=0: Fin 0 has no variables; f=1; `Fin 0 → Fin n` is a singleton. All
  finite basis ranks are one and the structural maps canonically identify
  the finite and full quotients with H.
- n=1: quotient evaluation at the parameters is inverse to the structural
  map. For m=n the exponent quotient is one and the displayed transition
  fixes generators; for m>n a transition need not be an isomorphism.
- Parameters equal to zero or nilpotent f: localization may be the zero ring.
  No `Nontrivial` localization hypothesis occurs. The spectra are then empty;
  their maps to the empty base spectrum and the singleton covering are permitted.
- Nonreduced and non-Noetherian H are included. For example, infinitely many
  polynomial variables over F_p and arbitrary repeated parameters impose no
  unrecorded regularity or finiteness assumption.
- As usual, exact `CharP H p` for prime p excludes H itself being the zero
  ring (its characteristic is one); this is the original characteristic-p
  hypothesis, not an added restriction. It does NOT exclude zero localizations.
- All quotient, localization, ring-map and scheme-test objects use the same
  arbitrary universe u. The index is the small subtype of the natural numbers;
  no smaller independent test-ring universe makes the colimit property vacuous.
- A basis over a zero localized ring is compatible with a nonempty finite
  index set; no argument infers nontriviality from its formal rank.

Searches recorded by the original submission (retained for this repair):

- `msearch.py ... leanfinder`: "Simultaneous roots of parameters indexed by integers
  prime to the characteristic form finite etale faithfully flat punctured tower
  and proetale covering". Eight hits including StandardEtalePair,
  StandardEtalePresentation and universal coprime factorization; no full tower theorem.
- `msearch.py ... loogle`: "MvPolynomial, Ideal.Quotient, Ring.DirectLimit".
  Zero hits; the service reports unknown identifier `Ideal.Quotient`.
- `msearch.py ... grep`: "parameter.*[Rr]oot|[Rr]oot.*[Tt]ower" in RingTheory.
  Five irrelevant hits concerning algebra towers; no simultaneous root tower.
- `msearch.py ... leansearch`: "Finite etale simultaneous parameter root algebras
  with power transitions and proetale inverse limit cover". Eight hits including
  `Algebra.Etale.finitePresentation` and etale composition/field structure; no full match.
- `rg` over both project roots for parameterRoot, parameter_root, ParameterRoot,
  PuncturedRoot, puncturedRoot, rootTower and RootTower. Found and read
  StrictLocalPrimeToPKummerSplitting (general finite quotient),
  StrictLocalKummerTameModule (actual full quotient), FullParameterRootTower,
  SNCUniversalResidualCharts, and root-tower puncture/lisse modules. These give
  constructions or results with extra geometric hypotheses, not this general theorem.
  The SNCParameterTower structure additionally demands connectedness of base,
  finite and full spectra, so it cannot replace this statement over arbitrary H.
- `rg` for the exact blueprint id and the proposed theorem/namespace in
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration or collision.
- Read the existing Q47 node and report and the current dependency records.
  Read Stacks algebra.tex at 00UB, 00UC and 090N and etale-cohomology.tex at
  03PL, including the finite-free unit-root calculation. They agree with the
  node's coefficient, root and puncturing hypotheses.

Original validation: the module-mode type probe and the full statement passed scompile.py
against both its private sandbox and the actual library module path. The first
full compile took 32.0 seconds and 25.7 seconds respectively, within the unchanged
60-second limit, with no reported errors or warnings. Final imports and the
complete delivery are subsequently checked by the prescribed dry run.

No statement correction and no STATEMENT-DISPUTED issue. The node changes only
in `lean` and by adding the already-landed definition node
`def-sfb-strict-local-kummer-tame-module` to `stmt_deps`. The main signature is copied verbatim from the module. All definitions
have real bodies, and the one theorem ends in `by sorry` as required at stage 2.

## Repair of return L, immutable head 2edac24b27b0

The return's sole defect was H2: `lem-sfb-strict-local-prime-to-p-kummer-splitting`
was a theorem statement dependency used only for the unrelated plain abbreviation
`AlgebraicGeometry.strictLocalParameterRootRing`. The maintainer explicitly offered
inlining the quotient via the polynomial and quotient definition nodes as a repair.
This packet follows that option: every use of that abbreviation, including the
coefficient ring of the iterated quotient, is replaced by its literal body. The
strict-local theorem import and its added `stmt_deps` entry are removed. The
localization API formerly obtained through that import is imported directly from
`Mathlib.RingTheory.Localization.Away.Basic`. No new notion or definition node is
introduced. All maps, laws, bases, covering clauses and edge cases are retained.

The retained saved packet first passed the prescribed dry run at 81e9af7cafa.
That mechanical success did not discharge the review defect, so this delivery
contains the actual source and dependency repair above. Current live metadata
was compared with the saved node: only `lean` and the added full-root definition
statement dependency differ. No natural-language statement or proof changed.
The finite quotient expansion was checked against the exact body at
`StrictLocalPrimeToPKummerSplitting.lean:58`; it is definitionally the same ring,
including the iterated quotient over H_n. `lean.statement` is regenerated verbatim
from the revised theorem signature. The returned eleven-step proof docstring and
all hypothesis/clause mappings above remain applicable after this expansion.

No statement correction, no dependency-module repair and no new node are required.
The maintainer's independent clause-by-clause reading from the return is retained
as the review of the unchanged mathematical content. No other agent was started.

Repair validation: `scompile.py` accepted the repaired delivered module in both
sandbox and library modes (25.7 s and 36.5 s). A separate scratch-only type probe
imports the repaired module and the old quotient abbreviation, restates the entire
returned theorem signature, and supplies the repaired theorem directly by `exact`.
It also passed both compiler modes (14.9 s and 9.1 s): Lean verifies that every
hypothesis and conclusion remains definitionally the same. The probe is not a
delivered module. A local record check confirms the signature is verbatim, only
`lean` and `stmt_deps` differ from the live node, the single added dependency is a
definition node, no strict-local theorem dependency remains, exactly one named
postponed proof remains, and every delivered Lean line is at most 100 characters.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
