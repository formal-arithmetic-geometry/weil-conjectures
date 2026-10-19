## Worker report

This delivery states `lem-sfb-divisible-extension-derived-reduction` in
`Sheaf.Paper.DivisibleExtensionDerivedReduction`. All theorem proofs are `sorry`;
all definitions contain actual data or choose objects determined by a stated
unique universal property. The node's natural statement is unchanged. There are
no new DAG nodes. The normalized sheaf scalar adjunction is a helper of the item. The landed
general derived-extension-of-scalars dependency record is unchanged.

The source read was the current main-20261015 Cartier proof, paragraphs 4 and 5
(and its final naturality paragraph), together with the item's ten proof steps.
I also read the local Stacks `definition-derived-tor` (06YU),
`section-derived-pullback` (06YV), and `lemma-derived-base-change` (06YY).
These supply the derived tensor machinery; the combined normalized statement is
the agent lemma recorded in the DAG, not a quotation of a single Stacks lemma.

Clause-by-clause rendering (names below are in `SheafOfModules.DivisibleReduction`):

- The small site is `{C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]`
  with `J : GrothendieckTopology C`; `[HasTerminal C]` gives the final object.
  Sheafification and locally bijective equivalences are explicit infrastructure
  instances in the coefficient universe. The site and coefficient universes are
  independent; `r` may be any universe containing a small model of the site.
  `SiteCoveringAxioms` is imported, and sheaves use its existing associated
  Grothendieck-topology presentation. No new site or sheaf category is defined.
- The integer and residue rings are `integers J` and `residues J n`, transparent
  uses of `constantSheaf J CommRingCat`, at `ULift ℤ` and `ULift (ZMod n)`.
  `projection J n` is the constant map of the actual lifted integer reduction
  homomorphism. The lifts only place the rings in the sheaf coefficient universe.
  Every assertion involving reduction assumes `hn : 1 ≤ n`.
- `Integral J` and `Residue J n` abbreviate the recorded `ringedSiteModules`,
  hence exactly Mathlib `SheafOfModules`; their derived categories use
  `DerivedCategory` with independent localization universes `wZ` and `wR`.
- `Presentation.S : ShortComplex (Integral J)` and `Presentation.exact : S.ShortExact`
  represent `0 -> B -> M -> F -> 0`, with `B = S.X₁`, `M = S.X₂`, `F = S.X₃`.
  The boundary is exactly `P.exact.singleδ`, the recorded short-exact triangle's
  canonical last arrow, with Mathlib's cone sign.
- `Presentation.H`, `i`, `wi`, and `kummer` specify the residue-module sheaf
  whose integer restriction is the kernel of `n : B -> B`. The short exact
  sequence `Res H -> B --n--> B` is a kernel presentation and entails the required
  epimorphy of `n`. The action is forced to be the natural residue action, since
  the ring map is locally surjective and additive maps commute with integers.
- `Presentation.Q`, `p`, `wp`, and `quotient` specify the actual sheaf cokernel
  `F --n--> F -> Res Q`. Its short exactness entails the required monicity of `n`.
  This is a categorical sheaf cokernel, not the quotient of global sections.
  These presentations impose no extra existence hypothesis: `presentation_exists`
  asserts their existence for EVERY short exact `S` under precisely `Epi (n • id B)`
  and `Mono (n • id F)`. Conversely their two exact sequences imply those hypotheses.
  Using presentations permits arbitrary choices of kernel/cokernel objects and
  does not replace a canonical construction by an arbitrary map.
- `D : DerivedChangeOfRingsCochainModel (projection J n)` is the dependency's
  universal derived change-of-rings pair: its ordinary objects and maps are the
  specified sheafified tensor, its counit computes on K-flat representatives, and
  its derived functor is `D.T`. Such models exist by the dependency theorem.
  Quantifying over a model does not assume a new tensor or an arbitrary functor.
- `Identifications.alphaF` states `Lq(F) ≅ Q[0]`; `alphaB` states
  `Lq(B) ≅ H[0][1]`. `quotient_unit` fixes the ordinary quotient identification.
  `kummer_unit` fixes the second identification by
  `eta_B ≫ Res(alphaB) = kappa_B`. `kappa` is the canonical boundary of `P.kummer`,
  transported by the canonical exact-restriction single and shift isomorphisms.
  `divisible_extension_derived_reduction` states existence and uniqueness of
  these normalized identifications. The uniqueness is the implicit canonicity
  of the source: the quotient is epic, and precomposition with the Kummer
  boundary is injective on endomorphisms of H because `Hom(B,H)=0`.
- `identifications` selects this unique object, not data from a bare existence
  statement. `boundary` is exactly `alphaF.inv`, then `D.T.map partial_S`, then
  the canonical shift comparison, then `alphaB[1]`, then `[1][1] ≅ [2]`.
  Thus it is the specified `d_(S,n)` in the RESIDUE derived category.
- `integerUnit` and `residueUnit` use Mathlib `SheafOfModules.unit`, so their
  underlying sheaves are the respective constant coefficient sheaves.
  `coefficientUnit` is the actual coefficient map, constructed from the compatible
  section 1 using `unitHomEquiv`. `coefficientIso_existsUnique` fixes
  `Lq(Z[0]) ≅ R[0]` by this unit; `coefficientIso` chooses that unique isomorphism.
- `boundary_adjunct` quantifies over EVERY `s : integerUnit J -> P.S.X₃`.
  Its unique `sbar` satisfies `coefficientUnit ≫ Res(sbar) = s ≫ p`, which is
  precisely reduction of s. The second conjunct identifies it with
  `coefficientIso.inv ≫ Lq(s) ≫ alphaF`. The third uses the normalized scalar
  adjunction's ACTUAL `homEquiv` on `coefficientIso.hom ≫ sbar[0] ≫ boundary`.
  Its right side is `s[0] ≫ partial_S ≫ kappa[1]`, followed only by the canonical
  restriction/shift identifications into `Res(H[2])`. This is the Kummer-type
  connecting image, including its sign, rather than an unspecified class.
- `boundary_natural` includes both identification squares and the boundary
  square for every `f : P.S -> P'.S`. Its maps `h` and `q` on the chosen torsion
  and quotient presentations satisfy exactly the kernel and cokernel squares
  `hi` and `hp`. The universal properties force these induced maps; the statement
  permits every presentation and every map of extensions.
- `inverse_image_natural` includes an arbitrary set-sheaf adjunction `U ⊣ V`
  with `[PreservesFiniteLimits U]`. Its lifts `UZ` and `UR` are exact module
  inverse-image functors, identified with U on underlying set sheaves by `eZ`
  and `eR`. `rho` is their constant-coefficient restriction identification.
  These are the induced inverse-image functors and identifications, not a tensor
  comparison assumed as a hypothesis. The theorem PRODUCES `e` for ordinary
  scalar extension, fixed by the ordinary unit equation, and `theta` for derived
  scalar extension, fixed by the displayed universal counit formula on K-flat
  representatives. It states shift compatibility of theta and gives the two
  identification squares and the reduced-boundary square. The target extension,
  torsion and quotient may be any presentations, with their canonical comparison
  isomorphisms `f`, `h`, `q` and the displayed kernel/cokernel squares. Thus the
  identity inverse image and arbitrary choices of target presentations are included.
  Applying the adjunction unit formula to these squares transports the displayed
  adjunct equality too; no separate equality of unspecified cohomology classes is used.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules` supplies the category and abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `Q`, and the standard localization/shift structure.
- `Mathlib.Algebra.Homology.ExactSequence` / `ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact`; and
  `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`,
  `ShortComplex.ShortExact.singleδ` and `singleTriangle_distinguished`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem,
  including `E`, `obj_eq`, `map_eq`, `T`, `ε`, `universal`, `computes`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the associated topology
  is the standard topology presentation used by every sheaf in this delivery.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- The general adjunction dependency's full source was read with
  `scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` has abstract
  internal modules as its domain and codomain. Its general interface matches its
  node and remains recorded unchanged. The item module supplies the sheaf-module unit normalizations as its own helpers.
- Mathlib `SheafOfModules.restrictScalars`, `SheafOfModules.unit`, `unitHomEquiv`,
  `Functor.mapDerivedCategory`, `mapDerivedCategorySingleFunctor`,
  `mapDerivedCategoryFactors`, `Adjunction.leftAdjointCommShift`,
  `shiftFunctorAdd`, and the ordinary tensor/restriction unit.
  The stated proof-dependency modules are imported without `public`, as required.

Edge cases checked mathematically before and during the reading:

- n=1: the residue ring, H, Q and the reduced boundary are zero; the constant
  coefficient unit and both normalizations still make sense. No `Nontrivial R`
  or primality condition is imposed. n=0 is excluded exactly by `1 ≤ n`.
- B=0, F=0, M=0 and a split extension: the canonical boundary is zero and the
  formulas give zero. There is no nonzero-object hypothesis.
- A point site, B=Q/Z and F=Z: the target is the actual n-torsion shifted by one;
  the unit is the Kummer extension boundary. B=Z fails the divisibility hypothesis;
  F=Z/n fails the injectivity hypothesis, so the lost cohomology is not silently dropped.
- Sheafification is retained in the quotient. No point, geometric stalk, enough
  points, scheme, boundedness, flatness of B or F, or constructibility is assumed.
- Source/target localization universes are independent, also for the second site.
  The coefficient universe contains a small site model; no site object/morphism
  universe equality is imposed. Every universe and variable is explicitly bound.
- The identity geometric inverse image and all target kernel/cokernel
  presentations are permitted; comparisons use the canonical single and shift
  maps, not identifications of objects by unrecorded definitional equalities.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `Derived tensor reduction modulo n of an extension by an n-divisible sheaf with n-torsion-free quotient and Kummer boundary`:
   eight hits, including `Algebra.Extension.tensorH1Cotangent`,
   `Rep.Tor_obj`, `Algebra.Generators.H1Cotangent.δ_eq`,
   `Algebra.Extension.tensorCotangent`, and `Rep.Tor_map`; none is this assertion.
2. `msearch.py ... loogle '"ShortComplex", "singleδ"'`:
   five hits. It found the exact canonical boundary `ShortExact.singleδ` and
   `mapShiftedHom_singleδ` naturality lemmas, which are reused; it did not find
   the derived-reduction/normalized-adjunction statement.
3. `msearch.py ... grep 'Bockstein|divisible|modulo' Algebra/Homology`:
   zero hits.
4. `msearch.py ... leansearch` with query
   `derived reduction modulo n of a short exact extension of abelian sheaves with n divisible kernel and n torsion free quotient`:
   eight hits, including general Ext exact-sequence lemmas,
   `HasDerivedCategory.standard`, `Abelian.Ext`, `Ext.homEquiv` and
   `ShortExact.extClass.congr_simp`; no exact match.
5. `rg` in `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for `DivisibleExtension|divisible.extension|divisible-extension-derived-reduction|reduction.*[Aa]dj|reduction.*[Ee]xtension`:
   general integral reduction/tower/adjunction and finite reduction declarations,
   but no matching node statement. The integral adjunction was read; it is tied
   to completed p-adic coefficients and does not apply to this arbitrary site.
   Plain `grep -rn` for the exact item id in `WeilConjectures` gave no hit.
6. Targeted source searches located the existing restriction, constant sheaf,
   canonical SES boundary, exact-functor comparisons, and shift-adjunction API.
   These are used directly rather than copied. No new independent notion/node
   was introduced by these searches.

The normalized sheaf scalar adjunction is a helper of the item in
`Sheaf.Paper.DivisibleExtensionDerivedReduction`. Its seven declarations are
`SheafOfModules.sheafScalarRestriction_exact`, `sheafScalarRestrictionLimits`,
`sheafScalarRestrictionColimits`, `sheafDerivedScalarAdjunction_exists`,
`sheafScalarOrdinaryAdjunction`, `sheafScalarDerivedAdjunction`, and
`sheafScalarModelCommShift`. Each carries the item's blueprint tag and is listed
in the item's `lean.declarations`. They give exact restriction, the ordinary
sectionwise unit, the derived K-flat unit formula, and the induced shift structure.
The general `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` is
imported publicly from `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`;
this also supplies `Adjunction.mapHomologicalComplex`. No dependency node is
included in this repair, and there is no separate helper module.

## Second reading by NA

This is the author's second reading; the independent review is the maintainer's
subsequent delivery review, as prescribed by the dispatcher. No second agent
was started.

I reopened the node and read each of its clauses against the complete module.
I checked B and F against `S.X₁` and `S.X₃`; all three short exact sequences;
residue-linearity of H and Q; both directions of the presentation equivalence;
the two reduction isomorphisms; the Kummer unit normalization; the precise
boundary composite; the reduction equation for every section; the Hom-adjunction
formula; and both extension and inverse-image naturality squares. The item helpers
were also reread against the complete abstract dependency:
the general declaration matches its node and remains recorded unchanged. The
sheaf-module unit formulas belong to this item and do not replace that interface.

The reading found and repaired a shift-interface problem: selecting the bare
triangulated structure from the change-of-rings existence model does not itself
specify compatibility of its shift comparison with the derived adjunction unit.
The helper now constructs the unique unit-compatible shift using
`Adjunction.leftAdjointCommShift` instead. The boundary and inverse-image
formulas use that structure. The comparison is not a theorem with an extra
assumption about an arbitrary chosen shift. I also checked the order of all
single/restriction comparisons in `kappa`, and the two shift comparisons in the
adjunct formula, against their full Mathlib signatures.

No statement correction or disputed statement is needed. Validation uses only
the prescribed `scompile.py` per-file wrapper and `deliver2.py` preflight.

## Returned delivery repair

The independent review of returned head `fd9655e802a4` requested three changes:

1. Removed the dependency-node copy from the packet, preserving the landed NN
   general record of `sk-def-sfb-derived-extension-of-scalars` on `newtargets-dag`.
2. Moved all seven helper declarations into the item module, retained their
   signatures and data, changed their blueprint tags to the item, listed all seven
   in `lean.declarations`, and copied all imports including the public upstream
   `DerivedExtendScalars` import. Removed the separate helper module.
3. Removed the dependency-modules section and described the normalized sheaf
   scalar adjunction as an item helper. No mathematical statement changed.

The initial saved-packet dry run passed mechanical checks as `554839018c`, but
still included the rejected dependency replacement. This repair addresses the
independent review rather than treating that mechanical pass as acceptance.

Repair validation: `scompile.py` compiled the single delivered module cleanly in
11.4 s (sandbox) and 12.4 s (library). The recorded main signature is exact, all
30 declarations are listed uniquely, all seven moved helpers have item blueprint
tags, and all Lean lines fit 100 characters. The item differs from the current
base only in `lean`; the dependency-node copy and separate helper module are absent.
