## Worker report

The module states `AlgebraicGeometry.finiteRelation_module_map_descent`. It uses the
inverse system of Noetherian rings and a limit cone, a finitely presented scheme over
stage `i`, a later stage `j`, finitely presented quasi-coherent model modules `Fj`, and
`n` specified equalities represented by pairs of maps indexed by `Fin n`. The hypothesis
`hrel` says each pair becomes equal after the canonical module base change to the limit
scheme. The conclusion supplies `j' ≥ j` where every equality already holds after base
change from stage `j` to `j'`.

The finite index of relations is `Fin n`; `src` and `tgt` choose source and target model
modules, and `lhs`/`rhs` are the two maps. `hFj_fp` and `hFj_qc` render finite
presentation and quasi-coherence. The ring-system, limit, affine-limit, finite
presentation, quasi-compactness and quasi-separatedness hypotheses are explicit binders.
The module base-change functor is `Scheme.Modules.moduleBaseChange` from
`Sheaf.AlgebraicGeometry.BaseChangeConventions`; the finite-presentation descent
statement is imported from `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent`.

Edge cases checked: `n = 0` gives a vacuous family of relations; `Fin n` handles any
finite collection, and no nonemptiness of the relation family is assumed. The Noetherian
assumption is retained as required by the source setting, although the proof argument
records that it is unused. No existing declaration matching the finite-relation
statement was found: searches used `msearch.py` leanfinder and loogle for finite
relation descent, grep of Mathlib and `WeilConjectures`, and `rg` over `lean/Sheaf`.

The dependency declarations are `AlgebraicGeometry.Scheme` (Mathlib), the convention
nodes `def-pc-morphism-conventions`, `def-pc-base-change`, `pqf-def-coherent`, and
`AlgebraicGeometry.finitePresentation_module_map_descent` from
`Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent`.

## Earlier second reading (a previous round; superseded)

The theorem signature was read against every clause of the node. The inverse-system and
limit data, stage inequality, finitely presented quasi-coherent module models, finite
family of maps, equality after limit base change, and eventual equality at one common
later stage are all represented. The finite family is encoded by `Fin n`; each relation
is a pair of maps with shared source and target, which is the direct map form of a finite
composite relation. No additional mathematical hypothesis beyond the source setting was
introduced.

## Second reading by J1

I read the sandbox node and theorem independently, and opened every statement
 dependency node and its recorded declaration. The local Stacks checkout is absent
 on this machine; I read the actual `limits.tex` source at
 https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex,
 label `lemma-descend-modules-finite-presentation` (Tag 01ZR), as well as
 [the rendered source](https://stacks.math.columbia.edu/tag/01ZR).
 It assumes affine transitions and qcqs stages; clause (3) concerns equality of
 maps between fixed finite-presentation modules. Our node specializes its base
 system to spectra of Noetherian rings and applies this to the system of base
 changes of `Xi`. No additional ambient field or characteristic is assumed.

The complete clause-by-clause checklist is:

| Object, hypothesis, or conclusion of the node | Lean rendering and verdict |
| --- | --- |
| Directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`; matches the directed-preorder convention, without requiring antisymmetry. |
| Noetherian stage rings R_i | `R : I ⥤ CommRingCat.{u}` and `[∀ k, IsNoetherianRing (R.obj k)]`; exact ring hypothesis, no field or domain restriction. |
| Inverse system S_i = Spec R_i, affine transitions, qcqs stages | `R.op ⋙ Scheme.Spec`; all stages and maps are affine automatically, so qcqs and affine-transition properties need no extra binders. |
| Limit S, affine | `c : Cone ...`, `hc : IsLimit c`, `[IsAffine c.pt]`; the projections are the compatible `c.π.app (op k)`. The unspecified ring R at the limit need not be separately chosen: affineness identifies the scheme with the spectrum of its global sections. |
| Fixed i and finitely presented X_i over S_i | `(i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))`, with `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` on f; matches the three-part project convention exactly. |
| Stage j at or after i, schemes X_j and X | `(j : I) (hij : i ≤ j)`; `pullback f (Spec.map (R.map (homOfLE hij)))` and `pullback f (c.π.app (op i))`; these are the prescribed fibre products. |
| Finitely presented quasi-coherent models of the collection | `Fj` in `X_j.Modules`, `hFj_fp`, `hFj_qc`; uses Mathlib's local finite-free presentation and quasi-coherence, not coherent modules or finite-dimensional vector spaces. |
| Given collection on X and identifications with the base changes | Canonical normal form: use the objects `(moduleBaseChange ...).obj (Fj k)` on X. An arbitrary given collection with its specified model isomorphisms transports to this form; simultaneous conjugation preserves equality and composition. Hence no additional restriction or missing descent assertion. |
| Finite collection of maps and specified composite equalities | `(n : ℕ)`, `src tgt : Fin n → M`, and `lhs rhs` are the evaluated composite maps for each relation. A composite is itself a module morphism; arbitrary pairs are also composites of length one. The theorem asks for neither new maps nor new identifications. |
| Equality after pullback to X | `hrel` equates the images under `moduleBaseChange f` along `Over.homMk (c.π.app (op j)) (c.w ...)`; exact equality, rather than just existence of an isomorphism of maps. |
| One common later stage | `∃ (j' : I) (hjj' : j ≤ j'), ∀ k : Fin n, ...`; the stage is chosen before quantifying over relations. Both sides are pulled back along the same `Spec.map (R.map (homOfLE hjj'))`. All equalities hold simultaneously. |

`M : Type u` indexes models and does not require that unused models be finite.
Only the finite image of `src` and `tgt` is inspected or appears in the result.
Restricting to that finite family gives exactly the node; conversely any such
family can be included among extra unused models without changing the assertion.
Likewise, replacing the original maps by their finitely many evaluated composites
loses no clause. These are equivalent data presentations, not a strengthened
conclusion. The signature is unchanged after this reading.

Dependencies were checked through their source definitions: `Scheme` extends a
locally ringed space with local affineness; `Scheme.Modules` is the sheaf-of-modules
category over its structure sheaf. The convention node has no separate declaration;
its three-part finite-presentation meaning supplies the three instances on f.
`BaseChangeConventions.moduleBaseChange` is explicitly
`Scheme.Modules.tensorPullback (baseChangeMap f g)`, so the map functors have the
correct direction and scalar extension. `pqf-def-coherent` explicitly uses Mathlib's
`SheafOfModules.IsQuasicoherent` for its quasi-coherent clause; its new coherent
predicate is not appropriate here and is not used. Mathlib's `IsFinitePresentation`
is local finite-free presentation and already implies quasi-coherence; the explicit
`hFj_qc` repeats the node's qualifier and adds no restriction.
I read `finitePresentation_module_map_descent`: its first conjunct descends modules;
its second descends maps between fixed models using canonical associativity of
tensor pullback. It is usable as the node's proof dependency; the present signature
does not itself refer to that theorem, so I removed its unused import and imported
Mathlib's `Quasicoherent` directly. No new definition node or dependency module
is necessary, and no statement correction is present.

Edge cases: `n = 0` imposes no equations and allows `j' = j`; an empty collection
is covered by empty `M` and `Fin 0`. An empty I cannot supply the explicitly fixed
`i` and `j`, exactly as in the node (there is no extra Nonempty instance). Empty
schemes and zero modules are allowed. Zero rings are allowed by `CommRingCat` and
Noetherianity. There is no characteristic, field, nonzero, or inhabited-module
hypothesis. The system index, rings, schemes, and module values use the same
arbitrary universe u, following the project limit convention; a finite collection
can always be indexed in this universe. No variable or universe is unbound.

Independent searches, using different wording from the first report:

- `msearch.py leansearch`: “Equality of homomorphisms between finitely presented
  quasi-coherent sheaves descends to a stage of an inverse limit”; service returned
  Internal Server Error, recorded as unavailable.
- `msearch.py leanfinder`: “Two morphisms of finitely presented modules equal after
  extension of scalars to a filtered colimit become equal at a common later stage”;
  eight hits. Opened `IsFinitelyPresentable.exists_eq_of_isColimit` and
  `Concrete.colimit_rep_eq_zero`: these concern a fixed category/colimit or elements
  of modules over a fixed ring, not sheaf base change over varying schemes.
  Other hits are the elementary module filtered-colimit construction.
- `msearch.py grep` on Mathlib/AlgebraicGeometry:
  `descend.*(equal|relation)|exists.*map_eq|colimit.*(hom|morphism)`;
  affine-limit section lemmas occur, not this finite module-map assertion.
- `rg` on `WeilConjectures/` and the project's `lean/Sheaf/`:
  `finite.?relation|relation.*descent|descend.*equal|module.*map.*descent`;
  the affine module-colimit lemma, ring-map descent, references to this node,
  and the two-clause module-map descent dependency occur. No existing declaration
  states this theorem. No private duplicate notion was introduced.

Mismatches repaired: the module lacked the standard copyright/license/author
header; its proof docstring compressed all four node steps into three generic
lines, omitting the finite affine cover, ring-colimit identification, presentation
and generator argument, entry lifting and vanishing, and persistence at a common
stage. I supplied these steps with the dependency node names and clarified the
composite/model-identification normal form. I replaced the unused theorem-module
import with the defining Mathlib import. Every theorem proof remains `by sorry`;
there are no definitions, hollow data, added axioms, or auxiliary proved lemmas.
The two inline proofs in `Over.homMk` only certify the base-ring triangle using
functoriality; they add no mathematical hypothesis or descent result.
