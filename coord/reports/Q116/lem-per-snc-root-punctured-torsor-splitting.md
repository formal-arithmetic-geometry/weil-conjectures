## Worker report

The module `Sheaf.AlgebraicGeometry.SncRootPuncturedTorsorSplitting` states
`AlgebraicGeometry.snc_root_punctured_torsor_splitting`, with its sole theorem proof
`sorry`. No definitions or additional hypotheses are introduced. The declaration docstring
carries all eleven proof steps of the node, with their named dependencies.

Source checked: ILO, Travaux de Gabber, Exposé IX Proposition 2.1, printed pages 133–134
(PDF pages 139–140), especially the strictly local parameter-root presentation and the
Abhyankar essential-surjectivity paragraph, specialized to invertible-order covers as in
IX 2.2. This is the node's scheme-theoretic splitting consequence. No normalization or
invariant-ring conclusion has been added.

Hypotheses and clauses, in order:

- `R : Type u`, `[CommRing R]`, `[IsRegularLocalRing R]`, and
  `[IsStrictlyHenselianLocalRing R]` give the strictly henselian regular Noetherian local
  ring. `IsRegularLocalRing` includes localness and Noetherianity. Its maximal ideal is
  `IsLocalRing.maximalIdeal R`.
- `r : ℕ`, `t : Fin r → R` permit every finite ordered parameter family, including zero
  parameters. `_ht` says each parameter lies in the maximal ideal.
- `_hparameters : ∃ s : List R, IsLocalRing.IsRegularSystemOfParameters
  (List.ofFn t ++ s)` states extension to a full regular system, using the recorded notion.
- `∏ i, t i` is the specified f; `Spec (.of (Localization.Away (∏ i, t i)))` is U.
- `G : Type v`, `[Group G]`, `[Finite G]` give the finite group with no restriction on its
  universe. `Nat.card G` is n, and `_hn : IsUnit (Nat.card G : R)` gives invertibility.
- `cover : Scheme.GaloisCoverAction G U` is the dependency's recorded finite etale
  torsor interface. Its data include the total scheme `cover.Z`, map `cover.π`, finiteness,
  etaleness, surjectivity, the group action over U, its laws, geometric simple transitivity,
  and quotient universal property. No connectedness of `cover.Z` is required.
- Each occurrence of `MvPolynomial (Fin r) R ⧸ Ideal.span (Set.range
  (fun i ↦ MvPolynomial.X i ^ Nat.card G - MvPolynomial.C (t i)))` is exactly the displayed
  B. It is an expression in the existing polynomial and ideal-quotient constructions,
  not a new definition. The existing downstream `sncParameterRootRing` abbreviation has
  exactly this expansion; importing its owning theorem would create a future proof-import
  cycle when that theorem uses this splitting lemma, so the expression is written directly.
- `Localization.Away (algebraMap R B (∏ i, t i))` is precisely B[1/f]. Its spectrum is U_B.
  The actual canonical map U_B → U is `Spec.map (CommRingCat.ofHom
  (Localization.awayMap (algebraMap R B) (∏ i, t i)))`. No arbitrary comparison is assumed.
- `pullback cover.π` along this canonical morphism is the actual P ×_U U_B.
- `∐ fun _ : G ↦ U_B` is the scheme disjoint union indexed by the given group itself.
  Finiteness makes this index small at the scheme universe, as confirmed by compilation.
- `∃ e : pullback ... ≅ ∐ ...` supplies the isomorphism, and
  `e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 _) = pullback.snd _ _` states exactly that it is over U_B.
  Neither equivariance nor normalization nor a quotient description is asserted.

Recorded statement dependency interfaces read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`, which
  extends `HenselianLocalRing` with separable closedness of the residue field.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring clause of
  `def-weil-regular-scheme`; the scheme clause `IsRegularScheme` is not needed here.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, whose definition says the list spans the
  maximal ideal and its length is the Krull dimension.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with ring structure
  and canonical induced ring map from `Mathlib.RingTheory.Localization.Away.Basic`.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `Scheme.GaloisCoverAction`, signature and all
  fields checked. `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, used through its
  field in that structure.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `X`, `C`; the quotient algebra
  structure is supplied by the existing Mathlib quotient construction. No evaluation
  map or polynomial universal-property lemma is needed in this statement.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.snd`; scheme instances come from `Mathlib.AlgebraicGeometry.Limits`, which
  also supplies the scheme coproduct. Statement dependencies are re-exported by the
  direct imports where needed; the available recorded proof modules have ordinary imports.

Edge cases checked: with r = 0, the empty product is 1 and the empty-variable quotient
is canonically R; the extension-to-parameters hypothesis still allows a full system s.
With n = 1 the roots give B canonically R and the one-element torsor splits. A finite
group has positive cardinality, so no n = 0 exclusion is being added. Repeated parameters
are excluded by extension to a genuine regular system, as in the source. Disconnected
finite torsors are allowed; no connected-space instance occurs. The zero ring is already
excluded by the source's local-ring convention. Arbitrary group and ring universes are
bound explicitly and no equality between them is imposed.

Searches made:

- `msearch.py leanfinder`, query “Finite etale torsor over punctured strictly henselian
  regular local ring trivialized by adjoining roots of parameters”: eight results about
  `StandardEtalePair`, `StandardEtalePresentation`, `Algebra.IsStandardEtale`, and
  `Algebra.IsEtaleAt`; none states the splitting theorem.
- `msearch.py loogle`, query `"Etale", "IsRegularLocalRing"`: zero hits.
- `msearch.py grep`, query `Abhyankar|punctured.*torsor|torsor.*splitt|sncRoot`: zero hits.
- `msearch.py leansearch`, query “finite etale torsor over strict henselian regular local
  ring splits after adjoining roots of parameters”: eight hits including
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod`, `HenselianLocalRing.TFAE`, and field
  Kummer splitting results; none asserts this local parameter-root torsor splitting.
- `rg` of `lean/Sheaf`, upstream `WeilConjectures`, and Mathlib for
  `sncRootPuncturedMap|snc_root_punctured_torsor_splitting|snc_root_punctured`: no hits.
  The direct upstream search for this node id also has no hits.
- Concept search of `lean/Sheaf` and upstream for root-algebra names found
  `Sheaf.DeligneLaumon.SncParameterRootQuotient.sncParameterRootRing` (declaration name
  `AlgebraicGeometry.sncParameterRootRing`), read in full. This is the same explicit
  quotient expression but its downstream theorem does not state this splitting lemma.
  `dag/lean_names_upstream.json` has no corresponding root-ring or splitting declaration.

Validation: `scompile.py Q116 lem-per-snc-root-punctured-torsor-splitting` compiled both
sandbox and library identities in 5.0 s and 4.9 s respectively, with no warnings or errors.
All work is in the assigned sandbox. No statement correction, new node, dependency repair,
or disputed assertion is needed.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
