## Worker report

The module `Sheaf.AlgebraicGeometry.ProperLimitNoetherian` states
`AlgebraicGeometry.exists_proper_limit_noetherian`. It introduces a directed nonempty
index type, inverse-system functors of schemes, a natural transformation of systems,
and limit cones for `X` and `S`. The hypotheses `[IsProper f]`, `[QuasiCompact (𝟙 S)]`,
and `[QuasiSeparated (𝟙 S)]` render properness and the qcqs base assumptions. The two
transition clauses quantify over every morphism in `Λᵒᵖ` and require `IsAffineHom`.
Each component is proper; each base component is locally of finite type and quasi-compact
(the scheme-level properties are represented by the identity morphism). The displayed
cone equation says that `f` is the limiting natural transformation. In the affine case,
for every ring presentation `S ≅ Spec A`, all base stages are affine and of finite type
over `ℤ`, and a cocone on the global-section diagram has colimit object `A`.

The declaration uses the recorded dependencies as follows: `IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`; `LocallyOfFiniteType` and `QuasiCompact`
from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `IsAffineHom` from the Mathlib
affine morphism property; `AlgebraicGeometry.exists_limit_affine_transition` from
`Sheaf.AlgebraicGeometry.LimitAffineTransition` is the project limit-system declaration;
`CategoryTheory.Limits.colimit`, `Cocone`, and `IsColimit` are Mathlib limits notions.
The conventions node is descriptive and contributes no declaration.

Edge cases checked: the index is only required nonempty and directed, so singleton and
empty-scheme cases are not excluded; no characteristic assumption is imposed; zero and
terminal schemes are allowed; the affine clause is conditional on an actual affine
presentation of `S`; the index universe is the scheme universe `u`.

Searches made: `msearch.py ... leanfinder "proper morphism over qcqs base is a limit of proper morphisms of finite type over Spec Z"` returned only Mathlib properness declarations (no match); `msearch.py ... loogle "AlgebraicGeometry.IsProper, CategoryTheory.Limits.IsLimit"` returned none;
`msearch.py ... grep` over Mathlib algebraic-geometry limit files found no proper-limit or
Noetherian-approximation declaration; `rg` over `WeilConjectures/` found no declaration
for this node (only unrelated finite approximations). DAG dependency records and their
source declarations were read before writing.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module signature clause by clause. The proper
morphism and qcqs hypotheses are the three instance binders; the directed nonempty
index and both inverse systems are explicit existential binders. The affine-transition,
proper-stage, finite-type-stage, limit-cone, and compatibility clauses occur as separate
conjuncts. The final implication is conditional on an affine presentation and includes
affine finite-type stages and the global-section colimit. No node hypothesis or
conclusion was omitted in rendering these clauses.

## Second reading by K1

I independently read the base node, sandbox node and Lean file, the signatures and
meaning of all six statement dependencies, and Stacks limits.tex 3346–3382 (0A0P)
and 1255–1277 (01ZA) on the server. I also read pione.tex 1848–1859 (0GS2), which
explicitly uses affine finite-type stages and A = colim A_i with the maps induced by
S = lim S_i. The source has exactly a proper f and a qcqs base; it assumes no field,
Noetherian base, finite presentation of f, or characteristic condition. The node
itself agrees with these sources and was not corrected. There are no new definition
nodes, dependency modules, or statement_change records in this delivery.

The clause-by-clause list below describes the repaired signature, not the previous
reading's verdict. All verdicts are exact after the repairs stated below.

| Node object, hypothesis or conclusion | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary schemes X and S | `{X S : Scheme.{u}}` | Exact; no field or extra structure |
| Scheme morphism f : X → S | `(f : X ⟶ S)` | Exact |
| f proper | `[IsProper f]` | Exact: separated, universally closed, locally finite type; universal closedness supplies quasi-compactness |
| S quasi-compact | `[CompactSpace S]` | Exact; repaired from the hollow identity-morphism condition |
| S quasi-separated | `[QuasiSeparatedSpace S]` | Exact; repaired from the hollow identity-morphism condition |
| A nonempty directed index set Λ | `∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))` | Exact directed-set convention; nonemptiness is part of directedness in the source |
| Inverse systems of X and S stages | `Xfun Sfun : Λᵒᵖ ⥤ Scheme.{u}` | Functor laws encode identity and composition of transitions |
| Compatible morphisms f_λ | `η : Xfun ⟶ Sfun` | Naturality is exactly commuting with the transitions |
| Both families of transition maps affine | Separate universal `IsAffineHom (Xfun.map α)` and `IsAffineHom (Sfun.map α)` clauses | Exact, including identity maps |
| Every f_λ proper | `∀ i, IsProper (η.app i)` | Exact |
| Every S_λ finite type over Spec ℤ | `∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (Sfun.obj i))` and `∀ i, CompactSpace (Sfun.obj i)` | Exact: the displayed terminal morphism targets Spec (ULift ℤ); compactness is equivalent to quasi-compactness of this morphism |
| X and S are their respective limits | `cX`, `cS`, `hX : cX.pt = X`, `hS : cS.pt = S`, and both `Nonempty (IsLimit ...)` | Exact; any limiting cone with the given vertex is representable this way |
| f is the limit morphism | `cX.π.app i ≫ η.app i = eqToHom hX ≫ f ≫ eqToHom hS.symm ≫ cS.π.app i` for every i | Exact compatibility; uniqueness follows from the base limit |
| If S = Spec A, the system may have affine bases | Universal conditional clause for `A : Type u`, `CommRing A`, and `S ≅ Spec (.of A)`, then `∀ i, IsAffine (Sfun.obj i)` | Exact: since the existence choices precede the conditional, an affine base gets an affine system; every presentation identifies the same base |
| A_λ finitely generated as rings | `RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Sfun.obj i))))` | Exact with A_λ = Γ(S_λ); an affine scheme is canonically Spec of this ring |
| A = colim A_λ with its induced maps | `Nonempty (IsColimit (Scheme.Γ.mapCocone cS.op))` | Exact: its vertex is Γ(cS.pt), identified with Γ(S) by hS and with A by the affine presentation; its maps are the global-section maps of cS.π |

Dependency reading: `IsProper` is the recorded Mathlib class in Proper.lean:41;
`IsAffineHom` is the exact all-affine-open preimage predicate (Affine.lean:47).
`LocallyOfFiniteType` and `QuasiCompact` are the recorded finite-type notions;
QuasiSeparated.lean:239–262 proves the scheme/morphism equivalences used here.
`specULiftZIsTerminal` (Mathlib AlgebraicGeometry/Limits.lean:55) gives the unique
structure morphism over ℤ without a smaller universe. The conventions node has no
private definition. `exists_limit_affine_transition` was opened in its project module:
it uses the same nonempty directed preorder, scheme universe, affine transitions and
limit cones, with canonical affine colimit projections. The category-colimit node
records Mathlib `Cocone` and `IsColimit`; `Cone.op` and `Functor.mapCocone` construct
the actual cocone here. No dependency record is unusable, and no notion is duplicated.
The upstream affine Noetherian approximation and `isColimitFgSubalgebraCocone` were
also opened; they approximate the base alone and do not state the proper-morphism item.

Mismatches found and repaired:

- H3: `QuasiCompact (𝟙 S)` and `QuasiSeparated (𝟙 S)` are true for every scheme,
  not the qcqs hypothesis. Replaced them by the actual scheme properties above.
- H3: `LocallyOfFiniteType (𝟙 (Sfun.obj i))` and identity quasi-compactness also hold
  for every scheme. Replaced the former by finite type over the canonical Spec ℤ
  morphism and the latter by compactness of the stage. For example Spec of a polynomial
  ring in infinitely many variables satisfies the old clauses but is not finite type
  over ℤ. Infinite disjoint unions show why identity quasi-compactness says nothing
  about compactness of the scheme.
- H3: an arbitrary cocone with colimit vertex equal to A did not require the maps to
  come from the displayed base limit cone or affine presentation. Replaced it by the
  canonical global-section cocone of cS; transporting its vertex identifies it with A.
- H8: the eight terse proof phrases omitted the distinct ninth affine step and the
  substance of the image-kernel and colimit computations. Expanded the docstring into
  the node's nine steps with the dependency names and the local ring computation.
- H9: added the standard project copyright header and used the usual `(· ≤ ·)` notation.

Edge cases: the empty index type is excluded exactly as in the source's directed-set
convention, whereas singleton indices are allowed. Empty X and empty S are not
excluded; the zero ring gives Spec 0 and a legitimate affine presentation, with finite
type over ℤ permitted. No n occurs; no positive-degree restriction is hidden. Arbitrary
characteristic and mixed characteristic are included. The scheme, index and affine
ring use the same arbitrary universe u, and Spec ℤ is lifted to u. There are no test
objects in a smaller independent universe. All variables and universes are explicitly
bound. No new definitions or axioms occur and the sole proof remains `by sorry`.

Independent searches (2026-10-11):

- LeanSearch via `msearch.py ... leansearch`, query “A proper morphism of schemes with
  quasi compact quasi separated target is an inverse limit of proper morphisms over
  schemes of finite type over the integers”: service unavailable (Internal Server
  Error); no verdict assigned to the unavailable search.
- LeanFinder via `msearch.py ... leanfinder`, query “a proper scheme map admits an
  inverse system of proper maps over finitely generated integer rings”: eight hits,
  properness classes/instances, finite iff proper and affine, and projective-spectrum
  properness; no matching statement.
- Loogle via `msearch.py ... loogle`, query `AlgebraicGeometry.IsProper,
  AlgebraicGeometry.LocallyOfFiniteType`: seven properness and Zariski-main-theorem
  declarations, no inverse-system approximation.
- `rg` on Mathlib AlgebraicGeometry, upstream WeilConjectures, project lean/Sheaf and
  `dag/lean_names_upstream.json`, using `proper.*(approximation|limit)`,
  `limit.*proper`, `exists_proper_limit_noetherian`, `NoetherianApproximation.ofIsAffine`,
  and `isColimitFgSubalgebraCocone`: no duplicate of the item. The hits were the base
  approximation and its ring colimit, the eventual-proper lemma, and the item's citers.
  Alternate searches for `QuasiSeparatedSpace`, `CompactSpace`, `toSpec`,
  `specULiftZIsTerminal`, and `mapCocone` located the existing notions used in the repair.

Validation: the repaired module compiled on the server in 1.7 seconds, exit code 0,
with no warnings. The sandbox node's lean.statement was regenerated verbatim from
the signature. The mathematical node and its other fields were left unchanged.
