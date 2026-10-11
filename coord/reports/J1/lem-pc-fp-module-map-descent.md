## Worker report

The module states `AlgebraicGeometry.finitePresentation_module_map_descent`.
It uses the directed poset `I` and a diagram `F : I ⥤ CommRingCat`; `Xi` is a
quasi-compact, quasi-separated scheme over the affine stage `Spec (F.obj i)`,
`X` is equipped with its map `u` to `Xi`, and modules are objects of the
project's `Scheme.Modules` category.  Finite presentation is Mathlib's
`SheafOfModules.IsFinitePresentation` (written as `M.IsFinitePresentation`),
and base change is `Scheme.Modules.tensorPullback` from the recorded base-change
conventions.

Clause (1) is rendered by the first existential: a later index `j`, a stage
scheme `Xj`, maps `u₁ : Xj ⟶ Xi` and `v : X ⟶ Xj`, and a finitely presented
module `Mj`, together with `i ≤ j`, the compatibility `v ≫ u₁ = u`, and an
isomorphism between the pullback of `M` and the pullback of `Mj`.

Clause (2) quantifies a stage `j`, maps `u₁` and `v`, finitely presented modules
`Fj,Gj`, and a map `φ` after pullback to `X`, with the compatibility hypothesis
`v ≫ u₁ = u`.  Its conclusion gives a later stage `j'`, transition map `w`,
comparison maps `u₂,v'`, a descended map `φj'`, canonical comparison
isomorphisms `eF,eG` for iterated pullback, and the commutative equation
`eF.hom ≫ (tensorPullback v').map φj' = φ ≫ eG.hom`.

Dependencies used: `def-pc-scheme` (Mathlib `AlgebraicGeometry.Scheme` and
`Scheme.Hom`), `def-pc-morphism-conventions` (convention node; no declaration),
`def-pc-base-change` (`AlgebraicGeometry.Scheme.Modules.moduleBaseChange` and
base-change declarations in `Sheaf.AlgebraicGeometry.BaseChangeConventions`),
and `pqf-def-coherent` (`AlgebraicGeometry.RingedSpace.IsCoherent`; the finite
presentation predicate itself is Mathlib's `SheafOfModules.IsFinitePresentation`).
The affine ring descent statement is `ModuleCat.finitePresentation_descent_directedColimit`
from `Sheaf.Algebra.FinitePresentationColimit` as the proof dependency.

Edge cases checked: `I` is allowed to be any nonempty directed poset; no
nonzero or characteristic assumptions are introduced, and zero modules are
covered by `IsFinitePresentation`.  The empty scheme is allowed by the stated
scheme binders.

Searches made: `leanfinder` for finite-presentation descent (found only
`SheafOfModules.IsFinitePresentation` APIs); `loogle` for
`SheafOfModules.IsFinitePresentation, ModuleCat.Hom` (no hit); Mathlib grep for
finite-presentation module colimit/descent (no theorem); `rg` in WeilConjectures
and the project Lean tree (no existing theorem with this node id or statement).

## Earlier second reading (a previous round; superseded)

The statement was checked against the recorded Stacks Tag 01ZR clauses and
compiled remotely with `scompile.py`; the dry-run preflight is the final check.


## Second reading by J1

Read the node, its three proof steps, each statement dependency and its Lean
record, and the actual dependency declarations. Read the Stacks source in
`/home/ubuntu/c1-stacks-review/limits.tex`, lines 2547–2613 (the local copy of
`literature/stacks-project/limits.tex`, lemma-descend-modules-finite-presentation,
Tag 01ZR). The source assumes a directed inverse system of qcqs schemes with
affine transitions; it has object, map and equality clauses. This node asks for
only the object and map clauses in the particular affine-base-change setting,
with Noetherian stage rings and Xi finitely presented over the fixed stage.
Those restrictions in the node are retained, even though 01ZR does not need
Noetherianity or local finite presentation. No node statement was changed.
The earlier Worker report describes the old signature; its mathematical
claims about the objects and canonical maps are superseded by this reading.

Object/hypothesis/conclusion list, with its final Lean rendering and verdict:

1. Directed index set I: `{I : Type u} [Preorder I]
   [IsDirected I (· ≤ ·)]`. This is precisely the project's directed-set
   convention for Stacks 00D3, including directed preorders. The fixed `i : I`
   already rules out the empty index set; no separate Nonempty hypothesis is
   necessary. PASS.
2. Noetherian affine stages Si = Spec Ri and their transition maps:
   `F : I ⥤ CommRingCat.{u}` and `hN : ∀ k : I, IsNoetherianRing (F.obj k)`;
   the affine stages are `Scheme.Spec.obj (Opposite.op (F.obj k))`, and their
   transition morphisms are `Scheme.Spec.map (F.map (homOfLE h)).op`.
   Contravariance has the direction Sj' to Sj for j ≤ j'. Affine schemes
   are qcqs and maps between affine schemes are affine. PASS.
3. S = Spec R = lim Si: `[HasColimit F]` and
   `Scheme.Spec.obj (Opposite.op (colimit F))`; its projections are
   `Scheme.Spec.map (colimit.ι F k).op`. The ring colimit is the stated R;
   Spec carries this colimit to the affine inverse limit. HasColimit records
   the existence of the object already stipulated by the node. PASS.
4. The fixed finitely presented Si-scheme Xi: `Xi : Scheme.{u}`, `fi` to
   Spec Ri, with `[LocallyOfFinitePresentation fi] [QuasiCompact fi]
   [QuasiSeparated fi]`. These are exactly the three conditions in
   def-pc-morphism-conventions for finite presentation, not merely qcqs. PASS.
5. X = Xi ×Si S with its projections: `X`, `a`, `b`, and
   `hX : IsPullback a b fi (Scheme.Spec.map (colimit.ι F i).op)`.
   IsPullback is Mathlib's universal-property characterization of the same
   fibre product used by def-pc-base-change, permitting an arbitrary choice
   of the product with its projections. It is not an unrelated scheme X.
   The unique projection-preserving isomorphism identifies it with the
   recorded `Limits.pullback`; no private fibre-product notion is defined.
   PASS.
6. Xj = Xi ×Si Sj for each j ≥ i: `j : Set.Ici i`, `Xj j`, `aj j`,
   `bj j`, and `hXj j : IsPullback (aj j) (bj j) fi
   (Scheme.Spec.map (F.map (homOfLE j.property)).op)`.
   The subtype stores exactly i ≤ j. As in (5), these are choices of the
   specified products, not extra geometric assumptions. PASS.
7. Module clause input: `∀ (M : X.Modules), M.IsFinitePresentation →`.
   This now quantifies the arbitrary given module on X, not a module on Xi.
   Mathlib IsFinitePresentation means locally the cokernel of a map between
   finite free module sheaves; its instance implies IsQuasicoherent, as read
   in Quasicoherent.lean lines 263–279. No redundant independent
   quasi-coherence condition or coherence/Noetherian condition on X is added.
   PASS.
8. Module clause output: existential `j : Set.Ici i`, `v : X ⟶ Xj j`,
   `Mj : (Xj j).Modules`, with both projection equations, finite presentation
   of Mj, and `Nonempty ((tensorPullback v).obj Mj ≅ M)`.
   The equations uniquely specify the canonical induced map from the limit
   base change to the stage base change, by the product universal property.
   This is precisely the descended module and isomorphism requested. PASS.
9. Map clause input: every `j : Set.Ici i`, the canonical map v specified by
   `hv₁` and `hv₂`, modules `Fj Gj : (Xj j).Modules`, their two finite
   presentation predicates, and every `φ` between their pullbacks on X.
   The order is stage, fixed models, then map on X, as in the node. Quantifying
   a projection-compatible v is equivalent to using the unique canonical v.
   PASS.
10. Map clause output stage: existential `j' : Set.Ici i` and
    `hjj' : j.val ≤ j'.val`, with `w : Xj j' ⟶ Xj j` and `v' : X ⟶ Xj j'`.
    Both projections of w and v' are prescribed; `hv : v' ≫ w = v`
    records the canonical composition equation. These requirements express
    the same base-change maps and add no arbitrary transition data. PASS.
11. Map clause descended morphism and its equality after pullback:
    `φj' : (tensorPullback w).obj Fj ⟶ (tensorPullback w).obj Gj`,
    `e : tensorPullback v ≅ tensorPullback w ⋙ tensorPullback v'`, and
    `e.hom.app Fj ≫ (tensorPullback v').map φj' = φ ≫ e.hom.app Gj`.
    Crucially e is required to equal the conjugate of
    `pushforwardComp v' w ≪≫ pushforwardCongr hv`, using the composite
    and direct canonical adjunctions chosen from
    `exists_tensorPullbackAdjunction`. The latter pins the tensor adjunction
    to its sectionwise unit formula (opened TensorPullbackAdjunction.lean).
    Read pushforwardComp and pushforwardCongr in Mathlib Modules/Sheaf.lean
    and conjugateIsoEquiv in Adjunction/Mates.lean: the former is sectionwise
    composition/equality and the latter reverses the isomorphism direction.
    Thus this is the canonical associativity comparison, shared naturally
    by Fj and Gj; it cannot be satisfied using arbitrary comparison isos.
    PASS.

Dependency reading: def-pc-scheme is Mathlib Scheme and Scheme.Hom, not a
restricted scheme category. def-pc-morphism-conventions is a convention node;
its finite-presentation clause is the three Mathlib morphism properties above.
def-pc-base-change uses the categorical fibre product and tensorPullback,
not Mathlib Scheme.Modules.pullback (a different construction).
BaseChangeConventions.lean and TensorPullback.lean were opened; the latter's
definitions have concrete inverse-image/change-of-rings/sheafification data,
with named theorem proofs, not hollow data. pqf-def-coherent's module and its
Mathlib references were opened: its quasi-coherence notion is precisely
SheafOfModules.IsQuasicoherent, already implied by IsFinitePresentation;
RingedSpace.IsCoherent is not being used as a substitute for finite presentation.
The affine proof dependency FinitePresentationColimit.lean was read: it is a
ring/module-colimit theorem, not an existing version of this scheme statement.
No new definition nodes or dependency modules are needed.

Edge cases: an empty I cannot have the fixed i, just as in the node; a singleton
I and stages j = i or j' = j are allowed. Zero modules and the zero ring are
not excluded. Xi, X, and any Xj may be empty schemes. Finite presentations
with zero generators or relations (n = 0) are included in Mathlib's predicate.
No field, nonzero, characteristic, separatedness, flatness or integrality
hypothesis was introduced. Index types, ring carriers, and schemes use the
same arbitrary universe u, so no independent smaller index/test universe is
being quantified. For any collection of these mathematical objects one can
choose a common universe; there are no unbound universe variables.

Independent searches (different queries from the first worker):
- msearch leanfinder: “A finitely presented sheaf on a scheme obtained by a
  filtered limit descends to one of the schemes” — eight finite-presentation
  predicate/local quasicoherent-data APIs, no limit-descent theorem.
- msearch loogle: `SheafOfModules.IsFinitePresentation` — the predicate,
  its constructors and local-data and quasicoherence instances, no descent.
- msearch grep: `(descend|descent|colimit|limit).*IsFinitePresentation|
  IsFinitePresentation.*(descend|descent|colimit|limit)` — no Mathlib hits.
- rg in all of WeilConjectures and lean/Sheaf for descend/descent with
  module/sheaf: constructible étale sheaf descent, flatness descent,
  fpqc descent, the ring-level affine statement and bounded-complex descent
  concern other notions/statements. None states this pair of scheme-module
  descent clauses. Exact-name rg in those trees and dag/lean_names_upstream.json
  also has no existing declaration with the delivered name.
These searches are recorded by msearch in searches.jsonl.

Mismatches repaired: the old given module belonged to Xi rather than X, making
its object clause vacuous by choosing j = i and Mj = M; the ring diagram did
not constrain X or any Xj, and later indices had no relationship to their
schemes; Noetherianity and local finite presentation were missing; arbitrary
comparison isomorphisms weakened equality of the descended map; and the
statement docstring lacked all three proof steps. The final signature fixes
all of these. Changed PartialOrder to the stipulated directed Preorder and
removed the redundant Nonempty binder and unused universe v. No mathematical
statement in the node, its proof, its sources or its dependency list was changed.

Validation: scompile.py compiled the repaired module on the server in 3.8 s,
exit code 0, with no warnings. Every variable and the sole universe u are
explicitly bound. There is one named theorem, whose proof is `by sorry`,
and no new definitions or proofs. Every line is at most 100 characters.
The node's lean.statement was copied verbatim from the final signature.

## Reviewer fix (R-fmd1209)

The delivered signature (ring colimit `colimit F`, arbitrary `IsPullback` choices of X and X_j indexed by `Set.Ici i`, bare `tensorPullback` along quantified maps v, w, v') was a second spelling of the setting of the pc descent family. Restated in the spelling of lem-pc-fp-complex-descent (G1 e47ee9280), which cites both clauses of this node in its proof: `R : I ⥤ CommRingCat.{u}`, cone `c` with `IsLimit` and `[IsAffine c.pt]`, `X = pullback f (c.π.app (op i))`, `X_j = pullback f (Spec.map (R.map (homOfLE hij)))`, `Scheme.Modules.moduleBaseChange` along `Over.homMk (c.π.app (op j))` and `Over.homMk (Spec.map (R.map (homOfLE hjj')))`; finitely presented quasi-coherent as `IsFinitePresentation` and `IsQuasicoherent` (hypotheses and conclusions). The canonical identification ((F_j)_{j'})_X ≅ (F_j)_X is the conjugate of `pushforwardComp ≪≫ pushforwardCongr` under the canonical adjunctions `Classical.choose (exists_tensorPullbackAdjunction _)`, the composition isomorphism of lem-weil-pbc-module-base-change-map-pasting. Compiled clean in lean/.sandbox/L.
