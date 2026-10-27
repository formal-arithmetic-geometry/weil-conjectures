## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSupportedKoszulLowLocalization` states
`AlgebraicGeometry.AlgebraicSpace.space_supported_koszul_low_localization`.
Its only postponed theorem is that statement, with its entire proof `sorry`.
The helper `spaceAffineEtaleKoszul` has real data: it extends the recorded
`ExteriorAlgebra.koszulComplex` along `ComplexShape.embeddingDownNat`, applies the
existing `affineScalarPullback` termwise, and localizes with `DerivedCategory.Q`.
This is the associated étale Koszul object, not a freely chosen object or functor.

Source read: `literature/stacks-project/spaces-perfect.tex`,
`proposition-detecting-bounded-below` (Tag 0GFI), especially the paragraphs
starting “Say V = Spec(A)” through the comparison on U and V, lines 7285–7313.
The proof docstring follows all five node proof steps. Its affine step uses a
bound b and truncates at b-1: the recorded affine quantitative lemma now has
this endpoint, which leaves this node's existential conclusion unchanged.
No statement correction or disputed mathematical statement is needed.

Hypothesis and conclusion correspondence:

- The universe convention is `universe u w`, `Scheme.{u}`, and explicit
  `HasDerivedCategory.{w}` instances for X, U, and the represented affine V.
  The existing small affine ringed models preserve the original section universe;
  no equality of independent site object and morphism universes is imposed.
- The base is `{S : Scheme.{u}}`; `X U : AlgebraicSpace S` are exactly the
  existing fppf-sheaf algebraic spaces, with their small étale structure sheaves.
- Quasi-compactness of X is `hXqc : CompactSpace (Point X.obj.obj)`.
  Its absolute quasi-separatedness is `hXqs : IsAbsolutelyQuasiSeparated X`:
  the recorded affine-test characterization of the absolute diagonal, with
  no quasi-separatedness assumption on S.
- The open subspace is presented by its inclusion `i : U ⟶ X` and
  `hi : IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) i.hom.hom`.
  This is exactly the scheme-test condition in `OpenSubspace`; presenting its
  algebraic-space source explicitly permits forming the derived module functors.
  This does not choose a different open-subspace predicate.
  `hUqc : CompactSpace (Point U.obj.obj)` is its stated quasi-compactness.
- The affine chart is `A : Type u`, `[CommRing A]`, `s : Spec (.of A) ⟶ S`,
  and `p : schemeSpace (Over.mk s) ⟶ X`. Thus V is Spec(A), with its specified
  S-structure. `hp : IsEtale p.hom.hom` means representable étale on all scheme tests.
- The reduced complement is `Z : ClosedSubspace X`, `hZred : IsReduced Z.val`,
  and `hZ : pointImage Z.val.arrow.hom.hom = (pointImage i.hom.hom)ᶜ`.
  Its defining existence/uniqueness is the recorded reduced-closed-support theorem;
  parametrizing it with these properties does not assume an extra complement.
- The elementary distinguished-square condition is
  `hZp : IsIso (pullback.snd p.hom Z.val.arrow.hom)`. This is precisely
  the projection V times_X Z to Z in fppf sheaves; algebraic spaces form the
  relevant full subcategory. It requires no extra scheme-structure identification.
- The underlying open of T=U times_X V is represented without choosing a
  fibre-product object by `schemePointMap p.hom.hom ⁻¹' pointImage i.hom.hom`.
  Both occurrences of its equality with the indexed union of
  `PrimeSpectrum.basicOpen (f k)` express exactly T=union D(f_k).
- The first conjunct `∃ (r : ℕ) (f : Fin r → A), ...` is existence of a finite
  list. The second conjunct is `∀ (r : ℕ) (f : Fin r → A), ... → ...`, so
  the conclusions hold for every such list, rather than just a chosen one.
- `spaceAffineEtaleKoszul A s r f` is B. The existing affine scalar pullback
  is the sheafification of O(W) tensor_A M, adjoint to the actual compatible
  scalar sections. On the affine it is the same associated étale module functor
  as `Scheme.Modules.affineEtaleAssociatedFunctor`, expressed on the canonical
  algebraic-space small model. It sends the recorded actual Koszul differential
  to its associated sheaf differential, and puts K_q in degree -q, including
  q=0; no arbitrary equivalence or noncanonical map is supplied as a hypothesis.
- B_X is literally `(derivedDirectImage p).obj (spaceAffineEtaleKoszul A s r f)`.
  Its perfectness is `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` on
  `X.smallStructureSheaf`: the existing local bounded finite-free-retract model
  predicate, with bounds and ranks allowed to vary over covering charts.
- `E : X.DerivedModules` and `X.derivedQCohProperty E` render exactly
  E in D_QCoh, using the existing module category and QCoh predicate in
  every cohomological degree. There is no boundedness or perfection input on E.
- The vanishing assumption is `∃ b : ℤ, ∀ j : ℤ, j ≤ b → Subsingleton (B_X ⟶ E⟦j⟧)`.
  A Hom group is zero precisely when its underlying type is subsingleton.
  This says all sufficiently negative integers, with no uniform bound over E.
- The output is `∃ a : ℤ, IsIso ((DerivedCategory.TStructure.t.truncLE a).map
  ((spaceDerivedAdjunction i).unit.app E))`. The map is the canonical normalized
  open-adjunction unit E to Ri_*Li^*E; because i is open its derived pullback
  is exact restriction i^*. This retains the actual morphism, not just existence
  of some isomorphism between the truncated objects.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, the small étale sites, structure sheaves, and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib `SheafOfModules.IsQuasicoherent` with the recorded slice instances.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`; its bounded local models
  use `StrictPerfectCoefficientPackageOnSite` and actual quasi-isomorphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, whose
  representable-open-immersion scheme-test condition is used for the explicit i.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`, and its existing `ClosedSubspace`,
  `IsReduced`, and `pointImage` dependencies.
- `WeilConjectures.AlgebraicGeometry.KoszulComplex`: `ExteriorAlgebra.koszulComplex`.
- `Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization`:
  `Scheme.Modules.affineEtaleAssociatedFunctor` and
  `exists_affineEtaleDerivedModuleRealization` (exact associated sheaf realization).
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleDerivedRestriction`, its canonical comparison with derived pullback,
  and the recorded base-change/cover calculus; the actual unit uses its public
  `SpaceAffineHomComparison.spaceDerivedAdjunction` interface.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, with its standard `truncLE` functor.
- Already landed definition owners added to stmt_deps:
  `def-sfb-space-affine-global-sections` (`SpaceAffineGlobalSections.affineScalarPullback`),
  `def-sfb-space-absolute-quasi-separated` (`IsAbsolutelyQuasiSeparated`),
  `def-a1-space-point-topology` (`pointImage` and the point topology),
  `def-sfb-space-derived-module-calculus` (`DerivedModules`, `derivedQCohProperty`,
  `derivedDirectImage`), `def-sfb-space-affine-hom-comparison` (`spaceDerivedAdjunction`),
  `def-trf-scheme-algebraic-space` (`schemeSpace`),
  `def-a1-algebraic-space-point-classes` (`Point`, `schemePointMap`),
  `def-sfb-space-closed-subspace` (`ClosedSubspace`),
  `def-sfb-reduced-algebraic-space` (`IsReduced`), and
  `def-sfb-space-small-ringed-model` (`SmallModules`, `smallStructureSheaf`,
  `smallModuleEquivalence`).
  These additions cite existing interfaces; no new definition node or dependency
  repair is necessary. All other fields of the item are unchanged.

Proof imports include the existing `DerivedEtaleZariskiEquivalence` and
`AffineKoszulLowLocalization` modules, and the Mathlib declarations for affine
qcqs and the principal-open basis/localization. The proof-only nodes
`lem-sfb-qcqs-space-fibre-product`, `lem-sfb-space-supported-etale-excision`, and
`lem-sfb-ringed-site-strict-perfect-local-actual` have no usable recorded Lean
module in the read snapshot, so no invented imports are added for them.

Edge cases checked before writing: r=0 gives the empty union and the unit
Koszul complex in degree zero; there is no positive-r or nonempty-list condition.
If U is empty, T is empty and the conclusion reduces to low vanishing of E;
if U=X, Z is empty and the open unit is already invertible. The zero ring gives
an empty affine chart and is allowed by `[CommRing A]`; X or S may be empty.
No nonzero ring, Noetherian, separated-space, characteristic, regular-sequence,
or finite-dimensional hypothesis occurs. Repetitions, zero elements, unit
entries, and redundant generators are allowed for f. A unit entry gives a
contractible Koszul object and overlap all of V, as expected. Hom vanishing uses
all integers j≤b rather than a finite interval. The one-step shift in the affine
quantitative input changes the chosen existential a, not this statement.

Searches for an existing statement (all via the prescribed msearch.py wrapper,
group Q139 and this item):

- leanfinder: “Supported Koszul complex in an etale distinguished square detects
  low truncation of derived open localization” — eight hits on generic
  truncations/shape support and etale loci; no geometric Koszul statement.
- loogle: `"Koszul", "trunc"` — zero hits.
- grep Mathlib: `([Kk]oszul.*(trunc|localiz)|[Ss]upported.*[Ee]tale)` — zero hits.
- leansearch: “Koszul supported etale neighborhood perfect pushforward detects
  low truncation open localization” — eight hits, including
  `RingHom.Etale.propertyIsLocal`, `HomologicalComplex.acyclic_truncLE_iff_isSupportedOutside`,
  and `CochainComplex.quasiIso_ιTruncLE_iff`; no match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `supported.*[Kk]oszul|[Kk]oszul.*(trunc|localiz)|lem-sfb-space-supported-koszul-low-localization`
  finds the affine Koszul upper/low-localization modules and scheme supported
  detector statements, but no algebraic-space statement of this node.
- rg of Mathlib, upstream names, `lean/WeilConjectures`, and `lean/Sheaf` for
  `SupportedKoszulLow|spaceAffineEtaleKoszul|space_supported_koszul` — zero hits
  before writing. No existing declaration is duplicated.

Validation: scompile.py compiled the sandbox and library module cleanly, 3.3s and
2.2s respectively, on the first pass. Final import/record changes are also checked
by the prescribed dry-run compilation below.

## Second reading by Q139

A separate reading pass compared the node and module clause by clause, including
the finite-list existence conjunct, the universal list quantifier, the actual
Koszul construction, the perfectness conjunct, the eventual-negative Hom bound,
and `IsIso` of the truncation of the actual canonical unit. No mismatch was found.
The explicit source U of a representable open immersion presents exactly the
open subspace condition. The reduced complement is supplied with exactly its
support and reducedness properties, and hZp uses the correct projection to Z.
The bound is existential, so the affine lemma's corrected endpoint b-1 is valid.
No source-based statement correction is needed. This is a self-check; no second
agent was started, as the dispatch brief explicitly prohibits starting agents.
The delivery remains subject to the maintainer's independent review.

Original delivery validation (superseded by repair validation below): `deliver2.py Q139 lem-sfb-space-supported-koszul-low-localization
--no-push` printed `OK (dry run): commit bb1bb790a8c passes the preflight and
compiles; nothing pushed`. The node delta was independently inspected: only
`lean` and the then-six appended `stmt_deps` differed. The ownership fault in
that original list is corrected in this repair.


## Repair of returned head e544980d9924

H2: replaced the statement dependency
`lem-trf-space-enlarged-etale-ringed-site-model` with the existing definition owner
`def-trf-scheme-algebraic-space`. Its existing:true record names exactly
`AlgebraicGeometry.AlgebraicSpace.schemeSpace` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`; the module and declaration are
unchanged. Read both its node record and the full declaration/docstring.
The owner list above is corrected accordingly.

Also implemented all four advisory owner citations: added
`def-a1-algebraic-space-point-classes` for `Point` and `schemePointMap`,
`def-sfb-space-closed-subspace` for `ClosedSubspace`,
`def-sfb-reduced-algebraic-space` for `IsReduced`, and
`def-sfb-space-small-ringed-model` for `SmallModules`, `smallStructureSheaf`,
and `smallModuleEquivalence`. Read all four records and their recorded source
modules. No new node or dependency module was created.

Compared the retained returned node with current main: there are no differences
outside `lean` and `stmt_deps`. Rebuilt the sandbox node from current main,
retaining the delivered Lean binding and the corrected dependency additions.
The Lean file is byte-for-byte the retained delivered version, as the return
requests; neither the mathematical statement nor its imports or proof changed.
This repair addresses dependency ownership only. The independent maintainer
already checked the mathematics and edge cases clause by clause in the return.

Repair validation: scompile.py compiled both sandbox and library module cleanly
(11.9s and 2.3s). The recorded signature matches the unchanged Lean file verbatim.
The node delta against current main is limited to `lean` and ten appended direct
owner dependencies; the incorrectly cited enlarged-site theorem is absent.

Repair dry run: deliver2.py --no-push printed
`OK (dry run): commit 418f4ebe19a passes the preflight and compiles; nothing pushed`.
