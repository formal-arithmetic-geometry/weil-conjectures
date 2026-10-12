## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality` by a complete
Lean proof from three strictly intermediate statements and the existing affine Koszul
power detection theorem. The argument constructs a distinguished triangle, uses the
supplied adjunction to prove pushforward orthogonality, transfers vanishing to the cone
using `Triangle.coyoneda_exact₃`, applies power propagation and affine detection, and
concludes with `Triangle.isZero₃_iff_isIso₁`. The converse uses injective postcomposition
by the invertible unit. No existing signature, definition, or public import changed.

Three new modules isolate restriction vanishing, power propagation, and the geometric
properties of the unit cone. Updated the original node's proof and proof dependencies.
The covering hypothesis is retained under a local name: the actual criterion concerns
only the affine scheme and its quasi-compact overlap, and the signature is preserved.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.koszul_open_orthogonality`
(`lem-pc-perfect-generation-koszul-orthogonal`). Its proof has no `sorry`.
This is a decomposition: one hole closed, three added, net −2 holes, not a completed
proof of the mathematical theorem independent of outstanding dependencies.

Every new hole, one per module:

- `AlgebraicGeometry.isZero_restrict_shift_koszul`
  (`lem-pc-koszul-restriction-zero`), in `KoszulRestrictionZero`.
- `AlgebraicGeometry.koszul_powers_orthogonal_of_orthogonal`
  (`lem-pc-koszul-powers-orthogonality`), in `KoszulPowersOrthogonality`.
- `AlgebraicGeometry.derived_open_unit_cone_properties`
  (`lem-pc-derived-open-unit-cone`), in `DerivedOpenUnitCone`.

The imported existing `AlgebraicGeometry.isZero_of_koszul_powers_orthogonal` remains
an outstanding dependency; its module was not edited. All three new statements have
source citations, complete prose proofs, and matching nodes. They were checked on the
empty tuple, empty open, whole spectrum, zero ring, and zero/unit generators: none
requires a nonempty spectrum, regularity, or nonzero generators. In particular the
power lemma allows arbitrary E, while the cone lemma has no Koszul hypothesis.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`
and the original direct proof dependency `lem-pc-ringed-spaces-derived-adjoint-general`.
The adjunction is already a parameter of the original theorem, and its `homEquiv`
suffices. Also removed the redundant explicit Mathlib ExactFunctor import from the new
DerivedOpenUnitCone module; DerivedCategory already provides its public API.
No other original imports or planned nodes were removed; affine detection
and the derived-category definitions remain used. No claim is made that the removed
module is absent from every other target's import closure.

## Where the brief, the DAG or earlier work was wrong

The planned argument suppresses three substantial interfaces: restriction of the
sheafified Koszul object is zero, orthogonality propagates to powers, and the cone is
both quasi-coherent and zero on the open. The last point needs quasi-coherence of
qcqs derived direct image, not merely the formal triangle argument. None of the two
original imported dependency statements provides these interfaces. The three new
lemmas make those steps explicit without weakening or repackaging the original
criterion. The unit route is unchanged; its realized record is empty, and the proof
retains the Stacks 09IR cone/Koszul-power route.

Read the source proofs at Stacks `perfect.tex`, lemma-orthogonal-koszul-complex,
and `more-algebra.tex`, lemma-koszul-mult and lemma-homotopy-koszul, from the available
local Stacks copy. Mathlib search was performed separately for every new statement
through LeanSearch, LeanFinder, and grep; LeanSearch returned Internal Server Error
and is recorded as unavailable. Searches of the library, DAG, and full blueprint
found no existing statement with these exact interfaces. The principal-unit lemma
concerns the truncated Koszul augmentation and requires all open-site derived
categories, so it cannot directly replace the restriction lemma here.

## New nodes

`lem-pc-koszul-restriction-zero`: `Sheaf.AlgebraicGeometry.KoszulRestrictionZero`.
Local contraction on each D(f_i), descent of vanishing, and exact restriction show
all shifts of K restrict to zero. This is independent of E and of the adjunction.

`lem-pc-koszul-powers-orthogonality`: `Sheaf.AlgebraicGeometry.KoszulPowersOrthogonality`.
The multiplication triangles and induction on the total positive exponents propagate
orthogonality. This statement concerns no open, unit, or quasi-coherence hypothesis.

`lem-pc-derived-open-unit-cone`: `Sheaf.AlgebraicGeometry.DerivedOpenUnitCone`.
For an arbitrary quasi-coherent E on an affine scheme, every distinguished triangle
of its open unit has a quasi-coherent cone with zero open restriction. There is no
Koszul object or orthogonality assumption. No data is chosen from an unproved theorem.

No change records or forced adaptations are needed.

## Second reading by V1

1. Compared the item with the repository using diff and checked the existing theorem
   signature byte for byte. Verdict: unchanged, with no altered hypotheses, conclusion,
   definitions, visibility, or original public imports. The three other modules are new;
   they contain only statements, not new data constructions. No change record is needed.
2. Compiled all four modules through lcompile.py in dependency order, without errors or
   warnings. A scratch copy with #print axioms for all four declarations reported only
   propext, Classical.choice, Quot.sound, and sorryAx. The latter is expected from the
   three new holes and the existing affine detection hole. Searched every delivered
   module: exactly three whole-proof public named theorem sorries, none in definitions,
   and no forbidden declarations or implementation attributes. Verdict: sound formal
   reduction, still dependent on open statements; this is not an axiom-free proof.
3. Read each new statement, docstring, and node against the local Stacks proof of
   lemma-orthogonal-koszul-complex and lemma-koszul-mult. Checked r=0 (empty union),
   U empty or whole, the zero ring, and zero/unit generators. Positive exponents are
   essential in the power lemma; no regularity or quasi-coherence of its E is needed.
   Quasi-compactness in the cone lemma ensures qcqs direct image preserves QCoh;
   uniqueness of right adjoints transports the assertion to the supplied R and adj.
   The derived counit is invertible, so the restricted unit and its cone have the
   asserted properties. All three statements are strictly parts of the argument,
   none a renamed orthogonality criterion. Repeated LeanFinder searches with
   contractibility, thick generation, and localization-triangle terminology, and grep
   for contracting Koszul triangles and invertible counits; no direct replacement.
   Also searched both library roots. The existing openRestriction_support_triangle
   gives an existential triangle on the open-scheme category, with different derived
   category binders, rather than the supplied over-site adjunction and arbitrary cone.
   The principal-unit theorem concerns the truncated augmentation and requires all
   open-site categories. Neither closes a new hole by a short application. Verdict:
   true, sourced, needed intermediate statements with complete prose proofs and nodes.
4. Read the formal argument from the theorem downward: hZ identifies the union,
   restriction and homEquiv prove pushforward orthogonality, shift adjunction and
   coyoneda exactness prove cone orthogonality, positive powers and affine detection
   kill the cone, and the zero-cone criterion proves the unit invertible. The converse
   uses injective postcomposition. All original public imports support the signature;
   each new proof-only import is used. The old proof_deps lose exactly the general
   derived-adjunction node, recorded under No longer needed. The unit realized record
   has empty statement/step entries; the Stacks cone/power route is retained. Verdict:
   actual reduction with accurate pruning, one hole closed and three added (net -2).
5. Compared the edited original node with its base: only proof, proof_deps and
   proof_origin change. Its steps name exactly the new reductions and existing affine
   detection used in Lean. Checked new-node source, searches, split status, created,
   blueprint ancestry, chapter/unit and Lean records; each recorded Lean statement
   matches its module byte for byte. Verdict: records agree with the delivery.

Second-reading changes: restored the original item's docstring instead of retaining
unnecessary edits to an existing declaration's documentation; removed the redundant
public Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor import from the new cone
module (it compiles with DerivedCategory alone); used mapsto lambdas in the item proof;
updated the pruning report. No signatures, mathematical reductions, or hole counts changed.
