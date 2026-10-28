# Repair the common-stage forward square

## Reason

The original `commonProjectionOpenPullbackTensor_forward` declaration asserted
an equality for arbitrary independent morphisms `mu` and `mu'`. The identity is
false: take all four categories to be `SingleObj (Multiplicative Bool)`, all functors and
comparison isomorphisms identities, and `mu`, `mu'` two different endomorphisms. The
compatibility equation is therefore an explicit premise of the repaired generic lemma.

## Old

```lean
theorem commonProjectionOpenPullbackTensor_forward
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {A' : Type v} [Category.{w} A'] {B' : Type v'} [Category.{w'} B']
    {F : A ⥤ B} {F' : A' ⥤ B'} {c : A ⥤ A'} {d : B ⥤ B'}
    (e : F ⋙ d ≅ c ⋙ F')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA')
    (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (M N : A) (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N))) :
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' := by
  sorry
```

## New

```lean
theorem commonProjectionOpenPullbackTensor_forward
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {A' : Type v} [Category.{w} A'] {B' : Type v'} [Category.{w'} B']
    {F : A ⥤ B} {F' : A' ⥤ B'} {c : A ⥤ A'} {d : B ⥤ B'}
    (e : F ⋙ d ≅ c ⋙ F')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA')
    (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (M N : A) (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N))) :
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' →
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' := by
  intro h
  exact h
```

## Users

`Sheaf.Paper.CommonProjectionOpenPullbackTensor` (held by nobody) is the sole user. Its
public statement is unchanged; its proof now imports the split concrete representative
compatibility theorem `commonProjectionOpenPullbackTensor_forward_compatibility`
(module `Sheaf.Paper.CommonProjectionOpenPullbackTensorCompatibility`, node
`lem-sf-common-projection-open-pullback-tensor-forward-compatibility`), passes that equation
to the repaired generic lemma, and then applies the existing inverse-square cancellation.
This adapted module is in the delivery.

## Status

landed 20261028T020732-L-2542850 2026-10-28 (merge of deliver/S3/Sheaf.Paper.CommonProjectionOpenPullbackTensorForward)
statement remains a named split-off `sorry` for a later worker.
