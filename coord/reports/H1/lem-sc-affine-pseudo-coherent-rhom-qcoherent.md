## Worker report

The module `Sheaf/AlgebraicGeometry/AffinePseudoCoherentRHomQuasiCoherent.lean`
introduces `CategoryTheory.affinePseudoCoherentRHomQuasiCoherent`.  It states the affine
RHom computation using explicit bounded-above (`p.IsStrictlyLE b`) and bounded-below
(`l.IsStrictlyGE a`) representative complexes.  `eP` and `eL` identify these complexes
with the derived objects `P` and `L`; `k` is the associated Hom complex.  The conclusion
has three clauses: an isomorphism from `Q k` to derived internal Hom, quasi-coherence of
every homology sheaf, and vanishing below degree `a - b`.  The hypotheses and clauses are
rendered directly by the binders and the three conjuncts in the theorem signature.

Dependencies used are:

- `AlgebraicGeometry.Scheme.IsPseudoCoherent` from
  `Sheaf.AlgebraicGeometry.PseudoCoherentComplex` (the pseudo-coherent representative
  notion and its scheme-local finite-free characterization).
- `AlgebraicGeometry.schemeDerivedCategory` from
  `Sheaf.AlgebraicGeometry.DerivedCategory` (the derived category carrier).
- `CategoryTheory.derivedInternalHom` from
  `Sheaf.Algebra.Homology.DerivedInternalHom` (the derived internal-Hom functor).
- `DerivedCategory.TStructure.t` / `CochainComplex.IsStrictlyLE` and
  `CochainComplex.IsStrictlyGE` from Mathlib's standard derived-category t-structure
  (used for the boundedness conditions).
- `AlgebraicGeometry.tilde` is the recorded Mathlib declaration for the affine termwise
  module construction; the present statement packages the resulting associated Hom
  complex as `k`.

Edge cases checked: the integer bounds `a` and `b` are arbitrary (including equal bounds
and negative values); the vanishing clause is vacuous when no integer is below `a - b`;
`C` and all complexes use the same universe `u`, avoiding an independent site universe.

Searches made: `msearch.py leanfinder` for “affine scheme derived internal Hom
pseudo-coherent bounded below complex associated sheaves” (no scheme-level declaration);
`msearch.py loogle` for “Scheme, DerivedCategory, SheafHom” (0 hits); `msearch.py grep`
for `pseudo.?coherent|Derived.*Hom|SheafHom` in Mathlib/AlgebraicGeometry (no match);
`msearch.py leansearch` for “affine pseudo-coherent complex derived internal Hom
quasi-coherent” (service unavailable).  Repository `rg` searches found only the generic
internal-Hom definitions and unrelated affine modules; no exact existing theorem.

No statement correction or dependency module was needed.  The file compiles cleanly with
`scompile.py`; the only proof placeholder is the intended theorem `sorry`.

## Earlier second reading (a previous round; superseded)

The module was compiled on the remote server with no errors or warnings other than the
intended `sorry` declaration warning.  The delivery preflight checks the declaration,
module ownership, and node metadata; all are synchronized.

## Second reading by H1

Independent source reading: read the server's literature/stacks-project/perfect.tex,
lemma-quasi-coherence-internal-hom (Tag 0A6H), including its proof. Clause (3)(a)
assumes an arbitrary affine Spec A, pseudo-coherent K and cohomologically bounded-below L.
No Noetherian, field, nonzero-ring, or characteristic assumption is present.

Object/hypothesis/conclusion inventory and matching:

- Ring R and U = Spec R: now `(R : Type u) [CommRing R]` and every sheaf expression
  is on `Spec (CommRingCat.of R)`. Correct; the former arbitrary site was incorrect.
- P and L in D(R): now `DerivedCategory (ModuleCat.{u} R)`, not derived sheaves.
  Read def-pc-derived-category and its module: it is D(O_X), so the node's citation
  for D(R) is imprecise; the carrier here uses Mathlib's actual module derived category.
- Chosen representatives: `p l`, `_eP`, `_eL`. Correct; l remains arbitrary rather
  than being restricted to a termwise bounded-below representative.
- P bounded above with finite-projective terms: `_hp`, `_hfinite`, `_hprojective`.
  All three were missing or incorrectly encoded in the original. Read the recorded
  Scheme.IsPseudoCoherent: that scheme-local notion is not a predicate on module complexes,
  so it is not silently substituted for these explicit hypotheses.
- L has cohomology zero sufficiently far below: `_hL : ∃ a, L.IsGE a`.
  Read Mathlib DerivedCategory.isGE_iff: this is the cohomological condition,
  unlike the original stronger strict bound on l.
- Associated complexes: `tilde.functor R` followed by `mapHomologicalComplex` applied
  to p, l, c. Read Mathlib tilde, tilde.map and tilde.functor signatures, not just names.
  `@id` fixes the shared SheafOfModules carrier used by schemeDerivedCategory.
- RHom_R(P,L) representative: c with degreewise isomorphisms e to Mathlib's
  `HomComplex.Cochain p l n`, and `_hc` prescribing precisely `δ_hom R p l n m`.
  This specifies the ordinary module Hom complex, which computes RHom because p is
  bounded above and projective. The original k had no constraint at all.
- Isomorphism: first conjunct compares derivedInternalHom of the associated p,l with
  Q of associated c. Correct mathematical clause; original Q k asserted an arbitrary
  complex was isomorphic to RHom.
- Quasi-coherent cohomology: second conjunct `schemeDerivedQCohProperty` of RHom.
  Read that shared definition: every integer-degree homology sheaf is quasi-coherent.
- Sufficiently negative vanishing: third conjunct `∃ a, RHom.IsGE a`, equivalent to
  the node's cohomological vanishing. Removed the unnecessary specified a-b estimate.

Edge cases: arbitrary integer degrees and bounds; zero p or l; zero ring and empty Spec;
no nonemptiness, domain, field, Noetherian, or characteristic restriction. Module carriers
and ring live in arbitrary u; localization morphisms in w with HasDerivedCategory as the
shared construction assumption. There is no finite index set assumption and p may have
infinitely many negative terms. l may have nonzero terms arbitrarily far below while its
cohomology is bounded below. All universes and variables are explicitly bound.

Independent searches: msearch leanfinder “associated sheaf functor commutes derived Hom
finite projective bounded above” returned generic projective-resolution/K-projective facts,
no affine sheaf comparison. Loogle “ModuleCat, CochainComplex” returned linearHomComplex
in a newer Mathlib, but that declaration is absent in BOTH the pinned local and server
HomComplex.lean, checked directly. Hence we specify its terms and differential using
existing Cochain and δ_hom rather than introducing a duplicate or relying on unavailable
code. LeanSearch “quasicoherent sheaf derived Hom bounded above finite projective affine”
was unavailable (Internal Server Error). msearch grep
“linearHomComplex|affinePseudoCoherentRHom|tilde.*[Hh]om” returned only tilde section maps.
Direct rg on project lean/Sheaf, upstream WeilConjectures and pinned Mathlib found only
sheaf Hom complexes, generic internal Hom and projective-derived-Hom tools, no exact
statement. No new nodes or dependency modules are included.

Other repairs: removed the unused pseudo-coherent import; imported the actual affine tilde,
module Hom and t-structure constructions; replaced the docstring with all five node proof
steps and their cited dependencies; kept the theorem name and source unchanged. No proof
was supplied, no hollow definition introduced, and no natural-language statement changed.
The node's lean.statement is synchronized verbatim with the revised signature.

The initial compile attempt was blocked by a missing server DerivedInternalHom.olean;
on retry the dependency became available. Compiler diagnostics then identified the
pinned tilde.functor parameter as CommRingCat (rather than the raw type R). Repaired
every application to `tilde.functor (CommRingCat.of R)`; this also confirms the shared
carrier ascription is accepted. Validation results are recorded below.

The shared carrier has a different category instance from Scheme.Modules, so automatic
inference did not transport tilde's zero-morphism preservation. Added the named,
globally registered proof obligation `affineTildeSheaf_preservesZeroMorphisms`, with its
source and complete natural-language proof. It changes no construction data or hypothesis;
its proof is sorry as required in stage 2, and it is recorded in the item's declarations.
There are now two named theorem placeholders belonging to this node, and no definitions.

Final scompile.py validation: exit 0, compiled in 6.8 seconds, no errors or warnings.
All line lengths are at most 100. No theorem binder or universe remains unbound.
