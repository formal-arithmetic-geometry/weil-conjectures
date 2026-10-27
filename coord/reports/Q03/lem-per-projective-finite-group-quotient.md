## Worker report

The delivery states `AlgebraicGeometry.exists_finiteGroup_quotient_of_quasiProjective`
in `Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient`. Its only postponed
proof is the theorem's `sorry`. The module docstring and theorem docstring name
Rydh's Theorem 4.4, Proposition 4.7 and Remark 4.9; the theorem docstring carries
all twelve accepted DAG proof steps, including their dependency ids. No definition
or theorem proof was introduced. The original mathematical statement, source,
proof, proof dependencies and all inherited metadata are preserved.

Hypotheses and conclusions, read against the node and the imported definitions:

| Node text | Lean rendering |
| --- | --- |
| B is a Noetherian scheme | `(B : Scheme.{u}) [IsNoetherian B]` |
| B is quasi-projective over an affine Noetherian scheme | `(S : Scheme.{u}) [IsAffine S] [IsNoetherian S]`, `(b : B ⟶ S)` and `hb : GabberModification.QuasiProjective b` |
| V is a scheme with V → B | `(V : Scheme.{u}) (p : V ⟶ B)` |
| V → B is quasi-projective | `hp : GabberModification.QuasiProjective p` |
| Quasi-projective means immersion into one finite-dimensional projective space | The imported `GabberModification.QuasiProjective` is exactly `∃ n : ℕ, ∃ i : Y ⟶ ℙ(ULift (Fin (n+1)); B), IsImmersion i ∧ i ≫ projection = p` |
| V → B is finite type | `[LocallyOfFiniteType p] [QuasiCompact p]` |
| A finite group H acts on V | `(H : Type v) [Group H] [Finite H] (a : H →* Aut V)` |
| The action is over B | `ha : ∀ h, (a h).hom ≫ p = p` |
| There is a scheme quotient over B | `∃ (Q : Scheme.{u}) (r : Q ⟶ B) (q : V ⟶ Q), q ≫ r = p ∧ ...` |
| q is invariant and finite | `IsAdmissibleFiniteSchemeQuotient a q` includes `IsFinite q` and `∀ h, (a h).hom ≫ q = q` |
| q is surjective | `Surjective q` |
| The quotient is geometric and has orbit topology | The same predicate includes `Topology.IsQuotientMap q` and its underlying-point orbit-fibre equivalence |
| Geometric fibres are orbits | For every algebraically closed `Ω : Type u` and `t : Spec Ω ⟶ Q`, the actual scheme `pullback q t` is nonempty, and for every pair of its points x,y there is h and the induced action map l carrying x to y. The two projection equations specify l uniquely as the base-changed action automorphism; it is not an arbitrary endomorphism |
| O_Q = (q_* O_V)^H | For every open W of Q, the imported predicate asserts injectivity of `(q.app W).hom` and that its image is exactly the invariant sections. The overlap restriction equations are the actual equality of pullbacks of sections, without identifying equal opens by an unrecorded cast. These canonical component maps are already natural, so this is the asserted sheaf identification |
| Categorical among schemes | For every `Z : Scheme.{u}` and invariant `f : V ⟶ Z`, `∃! g : Q ⟶ Z, q ≫ g = f`; Z is not restricted to B-schemes |
| Q → B is quasi-projective of finite type | `GabberModification.QuasiProjective r ∧ LocallyOfFiniteType r ∧ QuasiCompact r` |
| Projective V → B implies projective Q → B in the finite-space convention | `IsHProjective p → IsHProjective r`; these are exactly the recorded `def-kun-projective` predicates, not an ample-only substitute |
| If V is integral then Q is integral | `IsIntegral V → IsIntegral Q` |
| Every H-invariant open restricts to its quotient on the corresponding open | For every `U : V.Opens` invariant under all h, there exist `W : Q.Opens`, the restricted action `aU` and `qU : U.toScheme ⟶ W.toScheme`. The equalities `q ⁻¹ᵁ W = U`, action compatibility with U.ι, and `qU ≫ W.ι = U.ι ≫ q` fix the restricted construction. `IsAdmissibleFiniteSchemeQuotient aU qU` gives its finiteness, surjectivity, orbit topology and invariant sheaf; the last universally quantified unique factorization gives its categorical property. The geometric fibre assertion above restricts along this cartesian open square, so the restricted quotient also has geometric orbit fibres |

`IsAdmissibleFiniteSchemeQuotient` also records that point orbits lie in affine
opens. This is already a consequence of the given quasi-projectivity over the
specified ample base, as shown in accepted proof steps 1–2. It introduces no
new hypothesis or restriction: any quotient for this action satisfying the node's
conditions satisfies that admissibility condition as well. The finite geometric
quotient is unique by the explicitly stated categorical property. The invariant
open square is cartesian because its inverse image is exactly U, and hence its
geometric fibres are literally the corresponding fibres of q.

Dependency declarations read and used:

- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`; its finite coordinate type definition agrees
  with the node's finite-dimensional projective-space convention, including the
  empty-coordinate case (empty source embeds into P^0).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, nonempty with domain rings on nonempty opens.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` and `AlgebraicGeometry.IsNoetherian`.
  The latter is exactly locally Noetherian plus compact, as required here.
- Added already-landed statement dependency `def-per-gabber-modification-data`:
  `Sheaf.AlgebraicGeometry.GabberModificationData`,
  `AlgebraicGeometry.GabberModification.QuasiProjective` (lines 196–202), the
  general-base finite-projective-space immersion predicate. The upstream
  `AlgebraicGeometry.IsQuasiProjective` is confined to a field base and cannot
  express the present relative statement. We use the general predicate already
  landed today, rather than introduce a competing definition.
- Added already-landed statement dependency
  `def-per-admissible-finite-scheme-quotient`:
  `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`,
  `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`, whose complete
  definition and source docstring were read before using it.

The only node changes are the Lean attachment and adding these two already
landed definition dependencies, as permitted by brief-stage2 §5. There are no
new nodes, no dependency repairs and no statement correction. The resolved
stage-1 Q108 repair note was read; this delivery preserves the current accepted
Q83 split and does not restore a historical Lean attachment as accepted work.
The formerly deleted module/declaration name is available and is reintroduced
with the current full statement, not recovered from historical source.

All currently recorded proof-dependency modules are imported privately. The
independent orbit-tensor descent node `lem-per-orbit-tensor-line-descent` has
no Lean declaration yet, so there is no module to import for it. Its exact role
and the natural-language proof step remain in the theorem docstring.

Edge cases checked before writing:

- Empty V: Q may be empty; no Nonempty V assumption was added. Surjectivity of
  the empty map to empty is valid. There are no geometric points t of empty Q.
  Its projective-space embedding and the conditional integral conclusion are
  consistent; `IsIntegral V` itself forces nonemptiness.
- Empty B and empty affine base S are allowed; the zero ring is not excluded.
- The trivial group, ineffective actions and stabilizers are allowed. No
  freeness, faithfulness, order-invertibility, characteristic or normality
  assumptions occur. In the trivial case q can be the identity.
- The coordinate dimension can be zero; projective space has Fin(n+1)
  coordinates, so n=0 is P^0 and is not excluded.
- Invariant opens include bottom, top and opens that are not quasi-compact.
  There is no finite-type assertion about those restricted opens themselves.
- The common scheme universe u includes affine bases and geometric points of
  the same size as the schemes; the finite group has independent universe v.
  No extra equality of universes or small finite-group assumption was imposed.
- The overlap formula for invariants allows nilpotents and zero divisors;
  no localization-cancellation or reducedness assumption is encoded.

Searches performed before writing:

- `msearch.py ... leanfinder`, query: “A finite group acting on a
  quasi-projective scheme has a finite geometric categorical quotient which is
  quasi-projective”. Eight hits, including the categorical Galois-category
  finite-group colimit API, but no scheme quotient theorem matching this node.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsHProjective, MulAction, AlgebraicGeometry.IsFinite`.
  Zero hits; Mathlib's search does not know the project-specific
  `AlgebraicGeometry.IsHProjective` identifier.
- `msearch.py ... leansearch`, query: “Finite group action quotient scheme
  invariant structure sheaf projective quasi-projective”. Eight hits about
  set or representation quotients, no matching scheme theorem.
- `msearch.py ... grep` in Mathlib AlgebraicGeometry, query:
  `IsGeometricQuotient|IsCategoricalQuotient|QuasiProjective|quotient.*[Gg]roup`.
  Zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, query:
  `IsGeometricQuotient|IsCategoricalQuotient|IsQuasiProjective|exists_finiteGroup_quotient|finite.group.quotient|FiniteGroupQuotient`.
  Found the field-only quasi-projectivity predicate and the admissible
  finite-type field quotient theorem, which does not give relative
  quasi-projectivity/projectivity over the present base.
- `grep -rn` for this node id in `lean/WeilConjectures`: no match.
  The proposed theorem name also has no match in `dag/lean_names_upstream.json`
  or Mathlib AlgebraicGeometry.
- `rg` in the DAG and project sources for quotient predicates and for
  `def .*QuasiProjective|class .*QuasiProjective|HQuasiProjective` located the
  two already-landed reusable definition nodes above. No duplicate notion
  was introduced. `tools/blueprint_refs.py ancestor` reports
  `lem-per-artin-gabber-affine-curve`; the search for “quasi-projective” was
  also run.

The Rydh PDF referenced by the node was opened online, specifically pp. 20–23:
Theorem 4.4 supplies the invariant-affine existence criterion, Proposition 4.7
lists descent of finite type and (quasi-)projectivity over the stated Noetherian
bases, and Remark 4.9 gives the quasi-projective case. The stronger finite-space
interpretation here retains the node's ample-base hypothesis. The accepted DAG's
independent proof, rather than the paper's sketched graded argument, remains
verbatim in the docstring. No source file was written in the read-only clone.

Validation: `scompile.py Q03 lem-per-projective-finite-group-quotient` on the
single delivered module passed on the server with no errors or warnings
(module compile 3.8 seconds). Every universe and variable is explicit and
`autoImplicit` is false. Every line is at most 100 characters. The node's
`lean.statement` is extracted verbatim from the theorem keyword to before `:=`.
The prescribed `deliver2.py --no-push` dry run passed both server preflight
and compilation (initial checked commit `6f7a16c9302`). The delivery wrapper
repeats these checks on the final report before pushing.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
