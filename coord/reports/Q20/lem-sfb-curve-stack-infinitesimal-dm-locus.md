## Worker report

Stage 2 for `lem-sfb-curve-stack-infinitesimal-dm-locus`, Q20. The item is unchanged
apart from its Lean record and the addition of two definition dependencies. The prior
worker's stage-1 stale-assignment diagnosis does not apply: the live node is split and
reviewed, but has no Lean record, precisely the stage-2 entry condition. I have not
resplit its proof or changed a reviewed field.

The main module is `Sheaf.AlgebraicGeometry.CurveStackInfinitesimalDmLocus`, declaration
`AlgebraicGeometry.exists_curveStack_infinitesimal_dm_locus`. All three delivered
modules compile against the live published server build using scompile.py, separately
and in dependency order, with no errors or warnings. No global build or direct git
command was run. All theorem proofs in this delivery are `sorry`; construction data
are explicit.

Source read: moduli-curves.tex section-stack-curves (0DMJ), 0DSW
lemma-DM-curves, and the first paragraph of the proof of 0E6G
lemma-in-DM-locus-vector-fields, ending before the derivation identification.
I also read the algebraic-space morphism definitions in spaces-morphisms.tex:
03HE (quasi-compact), 03HL (separated/quasi-separated), 03ML (flat), 03XP (finite
presentation), 03ZM (proper), 06LR (relative dimension). The node's proof and source
specify 0DSM, 0DSN and 06N3 as its generic DM-locus and atlas inputs.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`. The base is `Spec (CommRingCat.of k)`.
- The specified category C is `ProperCurveModuli.category (Spec (.of k))`, an actual
  category over schemes over k, with algebraic-space sources, not only schemes.
  `ProperCurveFamily.space` uses the recorded `AlgebraicGeometry.AlgebraicSpace`.
  `projection` is a natural transformation to the actual representable presheaf.
- Flatness is `MapToSchemeIsLocally (@Flat)` on every representable etale scheme
  chart. Properness is separated diagonal (`IsRepresentableWith` closed immersion),
  quasi-compactness (`MapIsQuasiCompact`), locally finite type on the charts, and
  `MapToSchemeIsUniversallyClosed`, using closed point maps after every scheme base
  change. These are finite type = quasi-compact plus locally finite type, and the
  node's separated/finite-type/universally-closed algebraic-space convention.
- Finite presentation is the same quasi-compactness plus quasi-compact relative
  diagonal and `MapToSchemeIsLocally (@LocallyOfFinitePresentation)`. The diagonal
  condition is quasi-separatedness; it is not omitted merely because properness
  implies it. No chart itself is assumed proper, which would be incorrect.
- For every algebraically closed field in the big site's universe and every map to
  the base, the point space of the sheaf fibre product has `topologicalKrullDim ≤ 1`.
  The existing point classes and existing final atlas topology are used unchanged.
  Actual cartesian presheaf squares are `ProperCurveModuli.Hom.square`; identities
  and composition have exactly identity and composite maps. The category projection
  is `ProperCurveModuli.forget`, bundled by `BasedCategory.ofFunctor`.
- The maximal open is the existential `U : OpenModuliSubstack ...`. Its predicate
  selects a full subcategory. `fibred` retains the parent category’s fibred-in-groupoids condition; `pullback` gives stability under all arrows, hence
  under base change and isomorphism for this fibred category. `open_pullback` tests
  each scheme map and gives an actual open immersion W -> T and an equivalence of
  the 2-base change with h_W, compatible with the projection to h_T.
- Unramified relative diagonal is `HasUnramifiedModuliDiagonal U.category`. It gives
  a representing algebraic space for every pair of scheme tests, an unramified map
  to their product over Spec k, and compatibility with BOTH projections. This avoids
  replacing the relative diagonal by a stabilizer at one point or by an absolute
  diagonal. `SpaceMapIsUnramified` uses the recorded `IsUnramified` on etale charts.
- The scheme-atlas conclusion is exactly the dependency's
  `CategoryTheory.IsDeligneMumfordModuliStack U.category`: stack descent,
  algebraic-space diagonal, and an actual scheme whose atlas is representable,
  surjective and etale after every scheme test. It is a separate conjunct; the
  statement does not merely call an unramified diagonal “DM”.
- Maximality amongst opens with unramified relative diagonal is the first universal
  V clause, `HasUnramifiedModuliDiagonal V.category → V.IsContainedIn U`.
- An algebraically closed extension Omega/k is `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ Spec (.of k))`. Maps of field spectra are
  precisely field embeddings in the opposite direction, so this includes every
  extension in the given big-site size convention, not only algebraic extensions.
- A proper Omega-scheme of dimension at most one is `(C : Scheme.{u})
  (f : C ⟶ Spec (.of Ω)), IsProper f → topologicalKrullDim C ≤ 1 → ...`.
  No smoothness, nonemptiness, connectedness, stability or positive dimension is
  imposed. Over a field, proper finite-type schemes are finitely presented and flat,
  so they are objects of this precise category, including the empty scheme.
- `ProperCurveModuli.SchemePointIn U Ω a C f` says the represented scheme is
  isomorphic OVER Spec Omega to a member of the full open. Its isomorphism commutes
  with the actual structure map. This is presentation-independent point membership;
  it does not require a chosen representative of an isomorphism class.
- The iff's right side is `ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms`
  applied to the representable scheme presheaf. `dualBase` is the spectrum of
  `TrivSqZeroExt Ω Ω`, definitionally `DualNumber Ω`. `dualProjection` comes from
  ring inclusion, and `dualReduction` from the first-projection ring homomorphism.
  `infinitesimalReduction` is the canonical pullback lift; its data are not chosen.
  The predicate quantifies over natural automorphisms of the actual fibre product,
  requires identity reduction AND preservation of the dual-number base, and concludes
  equality with `Iso.refl`. It does not require fixing the projection to the curve,
  an erroneous strengthening that would rule out the infinitesimal automorphisms.
- The last universal V clause tests every `ProperCurveFamily (Over.mk a)` over every
  algebraically closed field, hence includes algebraic-space objects as required for
  ALL geometric points. Its hypothesis is membership in V implies the same
  identity-reducing condition. Its conclusion is `V.IsContainedIn U ∧
  IsDeligneMumfordModuliStack V.category`, giving both requested assertions.

Recorded dependencies read and reused:

- def-weil-field: Mathlib `Field` (Algebra.Field.Defs).
- def-sfb-stable-pointed-moduli-groupoids:
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`, especially
  `CategoryTheory.IsModuliStack`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`,
  `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`, `IsDeligneMumfordModuliStack`. Their full signatures and
  docstrings were read, including the scheme tests and their projection compatibility.
- def-sc-dual-numbers: Mathlib.Algebra.DualNumber, `DualNumber` and `DualNumber.eps`;
  the canonical inclusion and projection are `TrivSqZeroExt.inlHom` and `fstHom`.
- def-weil-unramified-morphism: Sheaf.AlgebraicGeometry.UnramifiedMorphism,
  `AlgebraicGeometry.IsUnramified`, exactly locally finite type plus open diagonal.
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `Scheme` and `Scheme.Hom`.
- def-trf-algebraic-space: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  `AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, and the actual presheaf data.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat, `Flat`.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  `IsProper`, `IsSeparated`, `UniversallyClosed`, with their finite-type convention.
- def-sbc-locally-finite-presentation:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation, `LocallyOfFinitePresentation`.
- def-weil-geometric-fibre: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback`; the extensions to spaces are actual sheaf products.
- def-kun-topological-krull-dimension: Mathlib.Topology.KrullDimension,
  `topologicalKrullDim`, with bottom for the empty space.
- def-sbc-smooth-morphisms: Mathlib's `Smooth`/`Etale`, already used by the recorded
  DM-atlas definition; no replacement atlas convention is introduced.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`;
  no algebraicity hypothesis `IsAlgClosure` is imposed on the arbitrary extension.
- Added definition's recorded dependency def-a1-space-point-topology:
  Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology, `pointTopologicalSpace` and
  `PointRepresentative.map`, using def-a1-algebraic-space-point-classes' `Point`,
  `PointRepresentative.Rel`, `schemePointMap`. Their signatures/docstrings were read.

The six proof-dependency nodes were read. None has a Lean record or Mathlib match
on the read base, so there is no recorded proof module to import. The theorem's
complete docstring records all six proof steps and their dependency node ids.
The definitions added here do not assume these theorems or their conclusions.

Edge cases checked before/during writing: empty curves and empty geometric fibres have
Krull dimension bottom and are allowed by ≤ 1; zero-dimensional proper schemes are
included; there is no reducedness condition on the curve or its automorphism group;
all characteristics and nontrivial field extensions are retained. For a curve with
nontrivial dual-number automorphisms the right side is false, not made tautological by
fixing the projection to the original curve. Finite reduced groups, alpha_p/mu_p in
characteristic p, and PGL_2 give the expected identity-test distinction. The empty open
has a pulled-back empty scheme atlas; no Nonempty/inhabited condition excludes it.
A substack diagonal map keeps both projections, essential even on a scheme stack.
The field and test-scheme universes are the same u; no independent smaller universe
can make the geometric tests vacuous. No `let` or `show ... from` occurs in a theorem
signature. Auto-implicit binding is disabled in all modules.

Searches: msearch.py leanfinder on the maximal DM curve locus returned only formally
unramified/smooth/etale SCHEME declarations, not a moduli-stack theorem; loogle
`"Stack", "Unramified"` returned zero hits; msearch grep
`CurveStack|OpenSubstack|DeligneMumford|AlgebraicStack` in Mathlib/AlgebraicGeometry
returned zero. Project rg searches found the recorded stable-moduli vocabulary and
scheme-only marked infinitesimal automorphisms; the latter cannot express the
algebraic-space geometric tests. The complete new-definition LeanSearch, LeanFinder
and grep outputs are recorded in each new node's mathlib_searches. DAG concept
searches found the corresponding statement nodes but no definition node for either
missing notion. blueprint_refs.py returned zero matches for “stack of curves” and
“open substack”. Existing point classes/topology were found and reused.

No statement dispute, correction, or unusable dependency record was found. The main
item's prose, proof and proof dependencies are unchanged. No existing dependency node
is rebound.

## New nodes

`def-sfb-proper-curve-moduli` supplies the actual category of algebraic-space curve
families, its base projection and its dual-number test. Source: Stacks 0DMJ/0D4Z and
0E6G, with the stated space-morphism conventions. This is not the existing stable
pointed category: no stability, markings, genus, projectivity, nonempty fibres or
purity may be imposed here. Searches in the DAG, Mathlib, WeilConjectures and Sheaf
found no declaration of this category. All space and scheme notions that already
exist are reused. The only postponed construction obligation is
`ProperCurveModuli.hom_operations`, which states cartesianness of the explicitly
specified identity/composition maps; proof irrelevance determines the proof fields.
Its source and full natural-language proof are in its docstring and its statement
is included in this definition node. No object is selected from an existence theorem.

`def-sfb-open-moduli-substack` supplies full open subcategories over schemes, their
inclusions and containment relation, the second projection of the recorded 2-fibre
product, and the precise unramified relative diagonal test. Source: Stacks 0DSM,
06N3, 050N, 003R and 04YM. The existing generic stack and DM definitions are used unchanged;
they did not supply opens or unramified diagonals. Searches found no such definition
node or Lean declaration. The postponed helper
`moduliTwoFiberSnd_projection` only proves the specified comma projection commutes
with the base; the underlying functor is explicit and uniquely fixed. Its statement
and proof are included in the new node and its source/proof docstring. No largest-open,
algebraicity, scheme-atlas or tangent criterion theorem is assumed in either new node.

Validation: the repaired deliver2.py --no-push run printed OK: all modules compile
and the full server stage-2 preflight passes. The initial six findings were only
grouped citation formatting in the new curve definition; all references now use
individual bracketed ids. The final source-reference wording names 04YM explicitly.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
