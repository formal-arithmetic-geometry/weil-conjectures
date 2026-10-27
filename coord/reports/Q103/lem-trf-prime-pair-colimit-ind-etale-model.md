# Q103: lem-trf-prime-pair-colimit-ind-etale-model

## Worker report

The module `Sheaf.RingTheory.PrimePairColimitIndEtaleModel` states
`RingTheory.prime_pair_colimit_indEtale_model`. Its only theorem has proof `sorry`;
there are no definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` field changes. The stage-1 split and its reviewed proof
remain verbatim. No repair note for this item exists in the read clone.

Sources read: `literature/stacks-project/more-algebra.tex`, Tag 0A02,
`lemma-henselization`, especially its category and colimit construction, and
Tag 0A03, `lemma-henselization-local-ring`, including the radical/locality
argument. The item's five proof steps are reproduced in the theorem's docstring,
including the extension from the chosen small skeleton, the algebra universal
property for the very same cocone, the idempotent radical argument, the principal
localization presentation of the specified localization map, and composition.

Each hypothesis and conclusion is rendered as follows:

- A commutative ring: `(A : Type u) [CommRing A]`.
- A prime ideal: `(p : Ideal A) [p.IsPrime]`.
- The specified localization `R = A_p`: `Localization.AtPrime p`; its structural
  map is exactly `algebraMap A (Localization.AtPrime p)`.
- The ideal `m = pR`: `IsLocalRing.maximalIdeal (Localization.AtPrime p)`.
  This is the same ideal by `Localization.AtPrime.map_eq_maximalIdeal`, supplied
  by the recorded localization interface. The field `k` is its quotient, so no
  arbitrary field or unidentified isomorphism is introduced.
- An object `B` is an `R`-algebra: `B : Under (CommRingCat.of R)`. Its structural
  ring map is `B.hom.hom`; the under category's morphisms are exactly the
  structure-preserving ring maps, hence all `R`-algebra maps.
- An object is etale: `AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom)`.
- Its structural closed-fibre map is an isomorphism:
  `Function.Bijective (Ideal.quotientMap (m.map B.hom.hom) B.hom.hom
  Ideal.le_comap_map)`. Bijectivity of this particular ring homomorphism means
  that this map is an isomorphism; it does not assert an unrelated quotient
  isomorphism. The full subcategory imposes exactly these two predicates.
- A small skeleton: `(I : Type u) [SmallCategory I] (_hI : Skeletal I)` and the
  equivalence `e` from `I` to that exact full subcategory. The skeletal condition
  is explicit and no filteredness or nonemptiness is assumed. The index universe
  is the ring universe, as required for these colimits.
- The chosen cocone and its structural map: `c : Cocone (e.functor ⋙
  ObjectProperty.ι _)`, with vertex `c.pt.right` and map `c.pt.hom.hom`.
  In this under-category cocone every component commutes with the structural
  map, recording the node's specified structural map and coprojections.
- Only the underlying ring universal property is assumed: `_hc : IsColimit
  ((Under.forget (CommRingCat.of R)).mapCocone c)`.
- Filteredness is concluded as `IsFiltered I`.
- Every stage is finitely presented: `∀ i : I,
  (e.functor.obj i).obj.hom.hom.FinitePresentation`. This is exactly
  `Algebra.FinitePresentation` for the algebra structure from that structural
  map, by the definition of `RingHom.FinitePresentation`.
- This same cocone is an algebra-colimit: `Nonempty (IsColimit c)` in
  `Under (CommRingCat.of R)`. This is the category of commutative `R`-algebras,
  through the standard `commAlgCatEquivUnder`; the data of `c` have not been
  replaced by any other cocone or by a bare colimit-existence assertion.
- The vertex `C = c.pt.right` is henselian local and its maximal ideal is `J=mC`:
  `∃ hC : HenselianLocalRing c.pt.right,
  @IsLocalRing.maximalIdeal c.pt.right _ hC.toIsLocalRing =
  m.map c.pt.hom.hom`. The explicit local-ring instance merely lets the
  conclusion mention the maximal ideal before a local-ring instance is known.
- The specified map `R → C` is local: `IsLocalHom c.pt.hom.hom`.
- Its structural map `k → C/J` is an isomorphism: `Function.Bijective` applied
  to `Ideal.quotientMap (m.map c.pt.hom.hom) c.pt.hom.hom Ideal.le_comap_map`.
- Each of `A → R`, `R → C`, and their specified composite is ind-etale:
  `RingHom.IndEtaleAcrossUniverses` applied respectively to the localization
  algebra map, `c.pt.hom.hom`, and their `RingHom.comp`. This uses the recorded
  dependency's canonical universe transport, without choosing another map or
  another algebra structure.
- There is no Noetherian, reducedness, domain, characteristic, or finite-type
  assumption on `A`.

The dependency declarations and their full signatures/docstrings were read:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` and
  `RingHom.FinitePresentation` (the latter unfolds to the former with
  `f.toAlgebra`).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  `Localization.AtPrime.map_eq_maximalIdeal`; the recorded `Ideal.ResidueField`
  is the quotient by the maximal ideal of this localization. The unused fibre
  ring clause of the dependency is not needed here.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, using
  exactly the affine spectrum-map predicate used by the pair-henselization node.
- `WeilConjectures.RingTheory.PairHenselization`:
  `RingTheory.pair_henselization`, whose full subcategory is used verbatim with
  base `R` and ideal its maximal ideal. Its generic existential pair-colimit
  does not assert the present theorem about this chosen skeleton cocone.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, and
  `CategoryTheory.IsFiltered` from the recorded category-colimit interface.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded
  `HenselianRing`, `HenselianLocalRing`, and strictly henselian interface. Only
  `HenselianLocalRing` is needed in the signature; it extends `IsLocalRing`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`, the canonical `RingHom.ulift` interpretation
  of the existing filtered-colimit predicate, publicly importing
  `Sheaf.RingTheory.IndPrincipalZariski` and the upstream `Algebra.IndEtale`.

The stated proof dependencies are imported too: the existing pair construction,
`WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations`,
`Sheaf.RingTheory.IndEtaleStability`, and Mathlib's affine ring-homorphism,
open-immersion and etale interfaces. No proof-dependency module is created or
changed, and no import cycle is introduced.

Edge cases checked before writing: if `A` is a field and `p=0`, then `R=A`,
`m=0`, the fibre predicate forces every object to be isomorphic to `R`, and the
conclusion specializes to the identity henselian field model. For `A=Z`, both
`p=0` and a nonzero prime are admitted. A non-Noetherian local base with its
maximal prime is admitted. The zero ring has no prime ideal, so it supplies no
case; the vertex cannot be zero because its quotient is the nonzero field `k`.
An empty `I` cannot be equivalent to this category since the identity algebra
is an object; nonemptiness is concluded through filteredness, not imposed as
an extra hypothesis. The same structural quotient map is used throughout.
All variables and the universe are explicit, with `autoImplicit false`.

Searches actually run in this attempt:

- `msearch.py`, `leanfinder`: "The colimit of etale algebras over a local ring
  with unchanged closed fibre is henselian local with maximal ideal extended
  from the base and is ind etale". Eight hits concern single etale maps,
  localization and etale loci; none states this entire cocone result.
- `msearch.py`, `loogle`: `HenselianLocalRing, CategoryTheory.Limits.IsColimit`.
  Zero hits.
- `msearch.py`, `grep`: `henselization|henselisation|IndEtale|ind_etale` in
  `RingTheory`. Zero hits in Mathlib.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item's blueprint id:
  zero hits. Searches for `pairHensel`, `pair_hensel`, `primePair`,
  `colimitIndEtale`, and henselian/ind-etale and pair-colimit combinations found
  the existing generic pair construction, its filtered-colimit properties and
  consumers. Their signatures were checked. None states this node's complete
  conclusion for the chosen skeleton ring cocone and all three specified maps.

There is no `STATEMENT-DISPUTED` issue and no mathematical node fault found.

Validation: the prescribed `scompile.py` compiled the delivered file against
the live published build with no errors or warnings (13.4 seconds for its
private sandbox check and 8.4 seconds for the library-module check). No local
compiler or global build was invoked. The dry run and delivery outcomes are
recorded by the required wrapper.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
