## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.QCohTruncationDerivedLimit`,
without changing their signatures or existing docstrings. Added the proof-only
import `Mathlib.Algebra.Category.Grp.Zero` to convert affine cohomology's
`Subsingleton` conclusion to `IsZero`.

The first proof supplies the affine-open basis and bound zero to
`AlgebraicGeometry.truncation_isDerivedLimitTriangle_of_local_bound`.
For each cohomology sheaf, `hE q` supplies quasi-coherence and
`AlgebraicGeometry.subsingleton_openModuleCohomology_of_isAffineOpen` supplies
vanishing. The existential product instance is proof-irrelevant, so the
resulting triangle is the specified one.

The second proof applies
`AlgebraicGeometry.Scheme.rightDerivedFunctor_isDerivedLimitTriangle` to the
first triangle. Its product comparison respects projections. Product
extensionality, the comparison's projection equation, functoriality and
`Pi.lift_π` identify the transported first arrow with the prescribed product
lift. Equality transport gives the required triangle. Explicit local instances
identify the dependency's `X.Modules` with the shared sheaf category, using
the existing instances rather than choosing another localization. A scoped
heartbeat limit accommodates unfolding these category instances; compilation
remains well below the 60-second limit.

The DAG's existing three-step argument is followed unchanged. No node edits,
new modules, statement changes or definition changes are needed. The unit
record `sk-thm-picard-duality` has no realized nodes that this proof bypasses.

## Proved and sorry left

Closed two original holes, both belonging to
`lem-pc-qcoh-truncation-derived-limit`:

- `AlgebraicGeometry.qcoh_truncation_isDerivedLimitTriangle`.
- `AlgebraicGeometry.rightDerivedFunctor_qcoh_truncation_isDerivedLimitTriangle`.

No `sorry` remains in the delivered module, and no new hole was added.
These are proofs from the existing named dependencies, as required by stage 3;
the still-unproved dependencies remain separate work items. In particular,
`AlgebraicGeometry.truncation_isDerivedLimitTriangle_of_local_bound` and
`AlgebraicGeometry.Scheme.rightDerivedFunctor_isDerivedLimitTriangle` retain
their existing holes outside this delivery.

## No longer needed

None. All three existing proof-only dependency imports are used. All existing
public imports support the statements and their instances. No DAG dependency
or module is pruned: the proof follows the original route.

## Where the brief, the DAG or earlier work was wrong

The derived-functor comparison uses `X.Modules` while this item's signatures
use the shared `SheafOfModules` carrier. Typeclass search alone does not find
the required source K-injective-resolution and localization instances.
Explicit `inferInstanceAs` local instances solve this without changing any
statement or introducing an alternate derived category. The remaining map
identification is proved by product projections, rather than assumed from
naturality.

The referenced blueprint unit source file is absent in this checkout; its
statement, steps and realized-node lists are present in the unit JSON and were
read there. This did not obstruct the proof.

## Second reading by M3

1. Compared the entire delivered module with the repository using `diff -u`.
   Both existing theorem signatures and docstrings are byte-for-byte unchanged;
   there are no definitions or new declarations. The only import addition is
   proof-only `Mathlib.Algebra.Category.Grp.Zero`. Verdict: pass.
2. Independently compiled the delivered file with `lcompile.py`: clean, 13.1 s.
   Compiled a scratch copy with `#print axioms` for both declarations: each
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from
   existing dependencies. No forbidden declaration mechanism or local `sorry`
   occurs in the delivery. Verdict: pass as a closure of two local holes over
   the existing open dependencies, not as an axiom-free completion of the target.
3. No statement was split off, and no new hole or node was added. Read the
   affine-vanishing, local-bound, and derived-functor comparison declarations.
   Affine vanishing applies with `p > 0`, for every cohomology degree, hence in
   particular for the negative degrees required by the local-bound theorem.
   Degree zero of the tower and arbitrary schemes (including the empty scheme)
   remain covered; neither proof assumes separation or boundedness. Verdict: pass.
4. Read top-down: the first proof chooses the affine basis and bound zero, then
   uses the existing local-bound theorem. The second uses the existing comparison;
   `Pi.hom_ext`, its projection identity, `Functor.map_comp`, and `Pi.lift_π`
   prove exactly the prescribed first-arrow equality. The explicit local
   resolution/localization instances are `inferInstanceAs` of the shared carrier's
   instances, not newly chosen derived categories. Searched the repository with
   truncation/limit/reconstruction variants, and ran `msearch.py ... grep` for
   `truncGE.*(isLimit|IsDerivedLimit)|truncation.*reconstruct` (zero hits).
   No shorter existing reconstruction theorem was found. All three proof
   dependencies are used and the public imports supply signature definitions,
   truncation operations, or product instances; no import or node is pruned.
   The unit `sk-thm-picard-duality` has empty realized lists, and its route is
   not bypassed. Verdict: pass.
5. Read `lem-pc-qcoh-truncation-derived-limit.json` and the unit record.
   Its first step is exactly affine vanishing plus the local-bound theorem;
   its second is the derived-functor comparison; its canonical-map step is the
   projection calculation. Existing `proof`, `proof_deps`, and documentary
   `proof_origin` agree with the implementation and require no edits. Verdict: pass.

Second reading changed only this report by adding the independent review;
no Lean repair was needed. Two original holes closed, zero holes added,
zero split-off statements, and no pruned modules.
