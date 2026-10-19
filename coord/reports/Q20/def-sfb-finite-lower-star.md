## Worker report

The node is already stated by the source declaration
`AlgebraicGeometry.ProEtale.lowerStar` in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`; no new module is needed.
The declaration is a noncomputable functor
`Sheaf (Scheme.ProEt.topology Z) A ⥤ Sheaf (Scheme.ProEt.topology Y) A`,
with implicit arbitrary schemes `Z Y : Scheme.{u}`, morphism `g : Z ⟶ Y`, and
coefficient assumptions `[Category.{u + 1} A] [Abelian A]
[IsGrothendieckAbelian.{u + 1} A]`. It is defined using the continuous base-change
functor `MorphismProperty.Over.pullback @WeaklyEtale ⊤ g` and
`sheafPushforwardContinuous`, exactly giving restriction of sheaves along base
change. The companion declaration
`AlgebraicGeometry.ProEtale.lowerStar_obj_val_obj` states the node's displayed
objectwise formula `(g_* G)(V) = G(V ×_Y Z)`.

The node's hypotheses and clauses match as follows. “A Grothendieck abelian
category A” is rendered by the category, abelian, and Grothendieck-abelian typeclass
binders. “An arbitrary morphism g : Z → Y of schemes” is rendered by the arbitrary
scheme binders and `g : Z ⟶ Y`, with no `WeaklyEtale` hypothesis. The base-change
functor between the small pro-etale sites is
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ g`; its continuity is the recorded
source instance `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`. The
pushforward functor and its restriction-on-sections formula are rendered by
`lowerStar` and `lowerStar_obj_val_obj` respectively.

Dependency used: `def-weil-pbc-proetale-site`, whose current declaration is
`AlgebraicGeometry.Scheme.proEtaleDerivedCategory` in
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`. The source lowerStar uses the
Mathlib/source pro-etale site `Scheme.ProEt` and its topology, the same site
recorded by that dependency; no private site definition is introduced.

Edge cases checked: `g` is arbitrary (including identity, non-weakly-etale, and
non-proper morphisms); the coefficient category may be any Grothendieck abelian
category; empty and terminal site objects are covered by the general sheaf
pushforward construction; and the objectwise formula applies to every site object
`V : Y.ProEt`.

Searches made:

* `msearch.py ... leanfinder "pushforward lower star sheaves pro-etale site base change"`:
  returned generic `SheafOfModules.pushforward*` declarations, with no exact
  `ProEtale.lowerStar` hit.
* `msearch.py ... loogle "AlgebraicGeometry.ProEtale.lowerStar, Sheaf.sheafPushforwardContinuous"`:
  returned no indexed hit (the source declaration is in the upstream checkout).
* `msearch.py ... grep "lowerStar" WeilConjectures` and direct `rg` in
  `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean` found the exact
  declaration and its docstring at lines 157–163, plus the objectwise lemma at
  lines 174–178.
* `msearch.py ... grep "lowerStar" Mathlib/AlgebraicGeometry` found no exact
  pro-etale lower-star declaration; Mathlib only supplies generic pushforward
  infrastructure.
* `rg -n 'def-sfb-finite-lower-star'` in both the project and source found no
  competing project declaration.

The exact source declaration is recorded in the node's `lean` field with
`existing: true`; therefore there is no module to compile.

## Earlier second reading (a previous round; superseded)

The node and source file were read independently. The source declaration has the
same arbitrary `g`, the same Grothendieck abelian coefficient assumptions, the same
small pro-etale source and target sheaf categories, and the same base-change
restriction construction. `lowerStar_obj_val_obj` supplies the displayed formula.
No hypothesis, object, or clause is added, dropped, weakened, or strengthened.

## Second reading by Q20

I reread the node statement, the recorded dependency, and the source declaration
`AlgebraicGeometry.ProEtale.lowerStar` (with
`AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback` and
`AlgebraicGeometry.ProEtale.lowerStar_obj_val_obj`) independently of the worker report.
The item-by-item comparison is:

1. The coefficient object, “a Grothendieck abelian category \(\mathcal A\),” is rendered
   by the source section variables `A : Type u'`, `[Category.{u + 1} A]`, `[Abelian A]`,
   and `[IsGrothendieckAbelian.{u + 1} A]`. Verdict: exact; no extra algebraic or
   finiteness hypothesis is present.
2. The schemes and morphism are rendered by `{Z Y : Scheme.{u}}` and
   `g : Z ⟶ Y`. Verdict: exact; `g` is arbitrary and there is no `WeaklyEtale g`
   assumption.
3. The base-change functor is rendered in the definition body by
   `MorphismProperty.Over.pullback @WeaklyEtale ⊤ g`, whose source and target are the
   small pro-etale sites `Y.ProEt ⥤ Z.ProEt`. Verdict: exact; the dependency
   `def-weil-pbc-proetale-site` is the recorded site notion, and its current
   declaration `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` explicitly uses
   `Scheme.ProEt` and `ProEt.topology` rather than introducing another site.
4. Continuity is rendered by the imported source theorem
   `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`, used by
   `sheafPushforwardContinuous`. Verdict: exact; continuity is supplied for every
   `g`, with no hidden properness, separatedness, or weak-etaleness condition.
5. The pushforward functor is rendered by
   `AlgebraicGeometry.ProEtale.lowerStar` with type
   `Sheaf (Scheme.ProEt.topology Z) A ⥤
   Sheaf (Scheme.ProEt.topology Y) A`. Verdict: exact source and target categories
   and the same coefficient category.
6. The displayed objectwise clause is rendered by
   `AlgebraicGeometry.ProEtale.lowerStar_obj_val_obj`:
   `((g)_*[A].obj G).obj.obj (op b) = G.obj.obj
   (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj b))` for
   `G` and `b : Y.ProEt`. Verdict: exact formulation of
   `(g_*G)(V) = G(V ×_Y Z)` on every site object; no quantifier or equality was
   dropped or strengthened.
7. The final “restriction of sheaves along base change” clause is rendered by the
   definition as `sheafPushforwardContinuous` applied to that functor. Verdict:
   exact; it is not a separately chosen or arbitrary functor.

The source file also confirms that the lower-star definition is noncomputable and that
its only coefficient assumptions are the category, abelian, and Grothendieck-abelian
instances above. The recorded source declarations are therefore usable as an
`existing: true` implementation; no module or proof is added.

Edge cases checked: identity `g`, non-weakly-etale and non-proper `g`, empty and
terminal site objects, empty covering families where permitted by the topology, empty
schemes, arbitrary coefficient universes `u'`, and zero objects of `A`. All are covered
by the generic site pushforward and by the universally quantified objectwise lemma;
no nonemptiness, characteristic, or finite-type assumption is introduced.

Searches were repeated with three independent forms. LeanFinder for “pushforward lower
star sheaves pro-etale site base change” returned only generic `SheafOfModules.pushforward*`
declarations and no exact pro-etale declaration. Loogle for
`AlgebraicGeometry.ProEtale.lowerStar, Sheaf.sheafPushforwardContinuous` returned no
indexed hit. Grep of Mathlib's `AlgebraicGeometry` found no pro-etale lower-star
specific declaration, while grep of the slopmaster2 source found the exact declaration
and companion continuity/objectwise declarations in
`WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean`; grep of the project
`lean/Sheaf` found no competing definition. Thus no mismatch was found and no file or
node field needed repair.

## Maintainer independent review correction

H2 mechanical correction: the delivered lean.statement used
`Scheme.ProEtale.topology`, whereas the existing declaration literally uses
`Scheme.ProEt.topology`. The complete replacement lean record corrects that spelling;
the mathematical statement and existing implementation are unchanged. The report's
matching signature above is corrected as well.

The category, abelian and Grothendieck-abelian instances listed above are the source
section context. Lean omits unused section instances from lowerStar: its construction
only needs the category structure and continuity, so it applies in particular to every
Grothendieck abelian coefficient category. This adds no hypothesis to the node.

Independent reproduction on 2026-10-16:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q20 def-sfb-finite-lower-star /home/ubuntu/weil-newtargets-Q20/lean/WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean`
passed locally through the private side overlay, exit 0, with no warnings or errors.
The wrapper reported 3.5 seconds for its sandbox and 4.3 seconds for the library file.
There is no delivered Lean module; this additional check validates the existing source.
No server fallback was needed. No global build or live Lean edit was performed.
