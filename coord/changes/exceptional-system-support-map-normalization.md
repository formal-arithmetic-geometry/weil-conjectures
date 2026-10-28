# Exceptional system support map normalization

## Reason

The assigned morphism equation is not enforced by `TransportCoreData`. Its `F`
field may be conjugated by arbitrary object automorphisms. The adjunction and all
required comparison isomorphisms transport along Mathlib's `isoCopyObj`, leaving
every object representative and every operation fixed. Thus the premise that the
object supports agree supplies no naturality of those identifications.

The delivery adds a fully defined datum update and proves a conditional obstruction
in the actual transport interface, plus a constructive normalization theorem. Given
a support comparison isomorphism and the object identifications, that theorem
constructs a new datum whose support functor equality is strict. It does not add a
normalization hypothesis to the original theorem or claim the original theorem proved.

## Old

The item had only the following public import and its one theorem with `by sorry`:

```lean
public import Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportObjects
```

The existing theorem's complete signature, docstring and proof body stay verbatim.
None of the declarations listed below existed. `TransportCoreData` itself is unchanged.

## New

Repair of returned head `5303952ac0c`: G7's landed delivery `296120256` derives
`TransportCoreData.reductionF` from `realizeF`. The former structure update failed
with "`reductionF` is not a field of structure `TransportCoreData`". Removed its
three-line `reductionF :=` assignment; the transported `realizeF` now determines
the conjugate's reduction comparison through the current API. All declaration
signatures and the original theorem stay unchanged.

The item adds this public dependency for the new definitions and their signatures:

```lean
public import Sheaf.CategoryTheory.FunctorObjectConjugation
```

The new module uses Mathlib's existing `copyObj` and `isoCopyObj` directly. It defines
only the normalization automorphisms and proves their strictification property.
All new declarations are below; section variables have the meaning recorded in
these modules and the self-contained natural-language node statements.

In `lean/Sheaf/Paper/ExceptionalRingTransportCoreLawsSystemSupportMaps.lean`:

```lean
def TransportCoreData.conjugateSystemF : TransportCoreData l Ω D hl c operation left
```

```lean
theorem TransportCoreData.conjugateSystemF_obj (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory) : ((d.conjugateSystemF l Ω D hl c operation left α).F E).obj K = (d.F E).obj K
```

```lean
theorem TransportCoreData.conjugateSystemF_map (E : FieldStage.{u} l) {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K') : ((d.conjugateSystemF l Ω D hl c operation left α).F E).map u = (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom
```

```lean
theorem not_unique_system_map_of_conjugation (E : FieldStage.{u} l) {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K') (hne : (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom ≠ (d.F E).map u) : ¬ ∀ d' : TransportCoreData l Ω D hl c operation left, HEq ((d'.F E ⋙ (sequenceProperty l E Y).ι).map u) ((d.F E ⋙ (sequenceProperty l E Y).ι).map u)
```

```lean
theorem not_forall_system_support_map_of_conjugation (E : FieldStage.{u} l) {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K') (hne : (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom ≠ (d.F E).map u) : ¬ ∀ d' : TransportCoreData l Ω D hl c operation left, (d'.F E ⋙ (sequenceProperty l E Y).ι).map u = eqToHom (exceptional_transport_core_system_support_obj l Ω D hl f c operation left d' E K) ≫ ((sequenceProperty l E X).ι ⋙ IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙ IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g).map u ≫ eqToHom (exceptional_transport_core_system_support_obj l Ω D hl f c operation left d' E K').symm
```

```lean
abbrev TransportCoreData.systemSupportFunctor (E : FieldStage.{u} l)
```

```lean
def TransportCoreData.normalizeSystemF (comparison : ∀ E : FieldStage.{u} l, d.F E ⋙ (sequenceProperty l E Y).ι ≅ d.systemSupportFunctor l Ω D hl c operation left E) (objects : ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory), (d.F E ⋙ (sequenceProperty l E Y).ι).obj K = (d.systemSupportFunctor l Ω D hl c operation left E).obj K) : TransportCoreData l Ω D hl c operation left
```

```lean
theorem TransportCoreData.normalizeSystemF_support (comparison : ∀ E : FieldStage.{u} l, d.F E ⋙ (sequenceProperty l E Y).ι ≅ d.systemSupportFunctor l Ω D hl c operation left E) (objects : ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory), (d.F E ⋙ (sequenceProperty l E Y).ι).obj K = (d.systemSupportFunctor l Ω D hl c operation left E).obj K) (E : FieldStage.{u} l) : let d' := d.normalizeSystemF l Ω D hl c operation left comparison objects d'.F E ⋙ (sequenceProperty l E Y).ι = d'.systemSupportFunctor l Ω D hl c operation left E
```

In `lean/Sheaf/CategoryTheory/FunctorObjectConjugation.lean`:

```lean
def comparisonNormalizer {D : Type u₃} [Category.{v₃} D] (J : B ⥤ D) (hJ : J.FullyFaithful) (G : A ⥤ D) (e : F ⋙ J ≅ G) (hobj : ∀ X : A, (F ⋙ J).obj X = G.obj X) (X : A) : F.obj X ≅ F.obj X
```

```lean
theorem copyObj_comparisonNormalizer_comp {D : Type u₃} [Category.{v₃} D] (J : B ⥤ D) (hJ : J.FullyFaithful) (G : A ⥤ D) (e : F ⋙ J ≅ G) (hobj : ∀ X : A, (F ⋙ J).obj X = G.obj X) : F.copyObj F.obj (F.comparisonNormalizer J hJ G e hobj) ⋙ J = G
```

The generic normalizer is the fully faithful preimage of the comparison component
followed by the inverse equality isomorphism. `conjugateSystemF` uses explicit
structure updates, adjunction transport, and whiskering. `normalizeSystemF` applies
that update using these normalizers. No definition chooses an arbitrary existence
witness and no new theorem has `sorry`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FunctorObjectConjugation | new module of X5 | Adds a construction and its proved normalization theorem. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportMaps | X5 | Adds datum updates, proved formulas, normalization, and conditional obstruction. Existing theorem unchanged and disputed. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport | unclaimed in the current server records | Sole existing direct importer. Its source and signatures remain unchanged; single-file compile checked against the delivered dependency chain. |

There are no existing users of the added names. No instance, attribute, existing
public import, existing definition or existing signature is changed. No target
statement or definition changes. The delivery tool also checks related modules.

## Status

landed 20261028T081804-L-2783973 2026-10-28 (merge of deliver/X5/Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportMaps)
