# AlgebraicGeometry.Scheme.adicFiniteAdjunction

## Reason

The first full-file compile with the new ordinary comparison exceeded the existing
60-second limit. Profiling showed substantial elaboration and kernel work in a
duplicate local scalar-adjunction construction. The existing proved private
`SheafOfModules.tensorAdjunction` in
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` supplies the same
adjunction. Separate compiled `rfl` checks confirm equality of both the old and reused
adjunction data and their presheaf-based Hom equivalences. The local Hom equivalence
reuses the existing smaller `tensorPresheafHomEquiv` directly; its section formula
remains `rfl`. A proved equation relates it to the reused adjunction.
The ordinary unit is also obtained from that adjunction and proved to have its
original insertion normalization. In the derived-unit proof the functor equality
transports only the quasi-isomorphism-preservation proof, rather than substituting
the functor throughout the existential construction.

The private `adicFinitePullChangeComparison` proof also gives its local natural
transformations by explicit components, reuses the naturality proofs of the original
composites, and states the final reassociation as one category associativity equation.
The two isomorphisms on complexes are also given by explicit components.
The new private ring-data constructor is explicitly `noncomputable` to omit
executable compilation; all of its fields and proofs are unchanged.
It retains its signature. Unused proof imports for the unfinished main theorem are
removed, with their complete list in the report; the main theorem's DAG dependencies
remain in place.

Both definitions below are private. Public statements, definitions, attributes,
imports and coefficient universes are preserved. No target meaning changes, and
no adopted `WeilConjectures` file is changed. The obsolete private presheaf
Hom-equivalence constructors and naturality proofs have no remaining caller.

## Old

```lean
private def adicFiniteHomEquiv {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (N : Mod S) :
    ((change f).obj M ⟶ N) ≃ (M ⟶ (res f).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).homEquiv _ _).trans
    (adicFinitePresheafHomEquiv f M N)

private def adicFiniteAdjunction {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) : change f ⊣ res f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := adicFiniteHomEquiv f
      homEquiv_naturality_left_symm := by
        intro M M' N a g
        apply (adicFiniteHomEquiv f M N).injective
        rw [Equiv.apply_symm_apply, adicFiniteHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun a b ↦ adicFiniteHomEquiv_naturality_right f _ a b }
```

## New

```lean
private def adicFiniteHomEquiv
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R) (N : Mod S) :
    ((change f).obj M ⟶ N) ≃ (M ⟶ (res f).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).homEquiv _ _).trans
    (SheafOfModules.tensorPresheafHomEquiv f M N)

private def adicFiniteAdjunction
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) : change f ⊣ res f :=
  SheafOfModules.tensorAdjunction f
```

## Users

`tools/downstream.py Sheaf.Paper.AdicConstructibleFiniteReductions --uses
adicFiniteAdjunction` and the corresponding query for `adicFiniteHomEquiv` each
list only this module. A repository search finds no external `import all` of it.
The local unit and adjunction-Hom proofs are adapted in this packet; the retained
section formula allows their other local consumers to retain their original proofs.
The private derived comparison uses the explicit component-map API described above.
No external module requires a forced adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicConstructibleFiniteReductions | A4 | Reuse the existing scalar adjunction and presheaf Hom equivalence; adapt the unit and adjunction-Hom proofs; prove the ordinary coefficient-square comparison. |

## Status

landed 20261021T024144-L-3038134 2026-10-21 (merge of deliver/A4/Sheaf.Paper.AdicConstructibleFiniteReductions)
