## Worker report

The module `Sheaf.CategoryTheory.ExactFaithfulTorsion` states
`CategoryTheory.exact_fullyFaithful_integerTorsion`. It also supplies the canonical
integer-kernel diagram, its cocone, and the torsion predicate that this node explicitly
introduces. These are helpers of this node, permitted by the human's missing-helper rule;
there is no new independent notion, new DAG node, or dependency repair. Every theorem,
including the named laws needed by the diagram definition, has only `sorry` as its proof.
Definitions contain actual kernel lifts, functor data, cocone data, and a proposition.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Two sites C and D | Independent `C : Type uC`, `[Category.{vC} C]`, `D : Type uD`, `[Category.{vD} D]`, with Grothendieck topologies `J` and `K`. The site dependency explicitly retains Mathlib's Grothendieck-topology sheaf encoding for the sheaf component. Only this component is used here, not coverings or cohomology. |
| Small in a common larger universe | `[Small.{w} C] [LocallySmall.{w} C]` and the corresponding two instances for D; both module universes are w. This is precisely smallness of objects and arrows relative to the chosen common value universe. It does not identify either site's object and arrow universes. In particular uC=t+1, vC=t, w=t+1 is allowed. |
| Abelian sheafification exists on both sites | `[HasSheafify J AddCommGrpCat.{w}]` and its K analogue. No `WEqualsLocallyBijective` or abelian-category hypothesis is added. The finite kernels used in the statement already exist for sheaves of modules. Smallness ensures the colimits asserted in the conclusion exist. |
| Ring sheaves R and S | `R : Sheaf J RingCat.{r}`, `S : Sheaf K RingCat.{s}`. Their universes are independent of each other and of the sites and module size. |
| A : Mod(R) -> Mod(S) | `A : ringedSiteModules.{w} R ⥤ ringedSiteModules.{w} S`, using the recorded abbreviation, transparently Mathlib `SheafOfModules`. |
| Additive | `[A.Additive]`. |
| Preserving kernels | The instance binder for every X, Y, and f is `PreservesLimit (parallelPair f 0) A`, exactly preservation of the equalizer of f and zero. Only kernel preservation is assumed; neither all limits nor exactness is substituted. |
| Fully faithful | `[A.Full] [A.Faithful]`. These say that all Hom maps are surjective and injective. |
| Having a right adjoint | `[A.IsLeftAdjoint]`; its definition is existence of a right functor with `Nonempty (A ⊣ right)`. No arbitrary candidate comparison or adjunction law is assumed. |
| Any module sheaf F | `F : ringedSiteModules.{w} R`. |
| F[n] for positive n | `(integerKernelDiagram F).obj n` is definitionally `kernel (n.val • 𝟙 F)`, with `n : PNat.DvdOrder`. The imported index is the existing positive-integer divisibility order. |
| The canonical inclusions for n dividing m | `integerKernelTransition` is `kernel.lift` of the earlier kernel inclusion. Its required annihilation is a named theorem; the lift data is not a choice from a mere existence theorem. Identity and composition laws are separately named statements. |
| The canonical map c_F | `c.isColimit.desc (integerKernelCocone F)` for a colimit cocone c. The cocone components are the actual `kernel.ι`. `Nonempty (ColimitCocone ...)` in the conclusion asserts existence for both diagrams rather than adding it as a hypothesis. |
| Canonical kernel identifications | `alpha : integerKernelDiagram F ⋙ A ≅ integerKernelDiagram (A.obj F)`, and for every n its hom component composed with the target kernel inclusion equals `A.map` of the source inclusion. The universal property of the target kernel makes this component unique. The natural isomorphism includes compatibility with every divisibility transition. |
| Induced colimit isomorphism | For every pair of colimit cocones c and d, `theta : A.obj c.cocone.pt ≅ d.cocone.pt`, with `A.map (c.cocone.ι.app n) ≫ theta.hom = alpha.hom.app n ≫ d.cocone.ι.app n` for every n. This characterizes the induced isomorphism uniquely and retains all choices of colimit. |
| Identifying A(c_F) with c_AF | `theta.hom ≫ d.isColimit.desc (integerKernelCocone (A.obj F)) = A.map (c.isColimit.desc (integerKernelCocone F))`. This is the node's c_AF theta = A(c_F), in Lean's left-to-right composition notation. |
| Underlying abelian torsion iff | `IsIntegerTorsion ((SheafOfModules.toSheaf.{w} R).obj F) ↔ IsIntegerTorsion ((SheafOfModules.toSheaf.{w} S).obj (A.obj F))`. The predicate means that a colimit cocone exists and its canonical map is invertible. Since colimits exist here and are uniquely isomorphic compatibly with their legs, this is equivalent to invertibility for the node's chosen colimit. It uses the actual underlying abelian sheaves, not a module-only substitute. |
| No uniform integer annihilator | No hypothesis or conclusion quantifies over one integer killing F. The entire positive-integer diagram is used. |

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`, `CategoryTheory.Precoverage.IsSiteForCoverings`:
  full declaration and docstring read; its documented Mathlib `Sheaf J` component is used.
  This theorem only needs the associated Grothendieck topology, not a presentation of its
  generating coverings. The module is imported as required by the dependency record.
- `Mathlib.CategoryTheory.Sites.Sheafification`, `CategoryTheory.presheafToSheaf`,
  `toSheafify`, and `sheafificationAdjunction`: full signatures and docstrings read;
  `HasSheafify` expresses the node's sheafification assumption.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  full signature and docstring read; used directly, with no copied module category.
  Mathlib `SheafOfModules`, its linear Hom, and `SheafOfModules.toSheaf` were also read.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, `CategoryTheory.Functor.Additive`:
  class and its signature read; used directly. This dependency is a Mathlib leaf and
  needs no `lean` repair.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, `ColimitCocone`, and `IsColimit.desc`: the actual colimit data and
  universal property. Using a supplied `ColimitCocone` rather than the globally chosen
  `colimit` preserves the same canonical-map semantics and avoids extra existence binders.
- Proof imports: `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
  `CategoryTheory.moduleSheaves_colimits_forgetful`, whose statement and proof docstring
  were read, and `Mathlib.CategoryTheory.Adjunction.Limits`,
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`, whose signature was read.
- `WeilConjectures.Data.PNat.DvdOrder`: the existing definition, `val`, `PartialOrder`,
  and `le_iff_dvd` were read. No replacement index category is defined.

Sources opened: `literature/stacks-project/sites-modules.tex`, labels lemma-abelian
and lemma-limits-colimits (lines 1336-1400), and `categories.tex`, label
lemma-adjoint-exact (around lines 3471-3510). The complete seven-step proof from the node
is rendered in the main declaration's docstring. Every postponed construction law also
has its source, blueprint id, and complete natural-language proof.

Edge cases checked before writing:

- n=1 gives the zero kernel of the identity. It is retained as an index object.
- The zero sheaf and zero coefficient ring give zero kernels and colimits; the statement
  still includes them. The zero functor on a nonzero category fails full faithfulness,
  so it cannot incorrectly reflect torsion under these hypotheses.
- On the one-point site, a torsion-free nonzero group has all integer kernels zero and
  fails the torsion predicate. Q/Z satisfies it while having no uniform exponent.
- The empty site has the zero module category and is allowed: no nonempty-site binder.
- Site object and morphism universes can differ; the theorem compiled with independent
  uC, vC, uD, vD, r, s, w. Smallness relative to w expresses exactly the common universe.
- Identity and repeated divisibility transitions are included. No bound on n is imposed.
- The comparison equations fix the maps, not just isomorphism classes of source objects.

Searches actually run (the msearch calls are in sandbox `searches.jsonl`):

- LeanFinder: `An additive fully faithful left adjoint preserving kernels preserves and
  reflects integer torsion given by colimits of kernels of multiplication by positive
  integers`. Eight hits, concerning Bousfield/Serre localizations, abelian transfer, and
  finite-limit preservation; none states this theorem or defines the general diagram.
- Loogle: `CategoryTheory.Functor.Additive, CategoryTheory.Limits.kernelComparison`.
  Zero hits for this combined query. The supporting Additive and kernel-comparison
  declarations were then inspected directly in Mathlib.
- msearch grep in CategoryTheory:
  `torsion.*(colimit|faithful)|(colimit|faithful).*torsion`. Zero hits.
- LeanSearch: `integer torsion kernel diagram colimit exact fully faithful left adjoint`.
  Eight hits about kernel/cokernel cocones, Serre localization, and colimit data; no match.
- `rg` over project `WeilConjectures` and `Sheaf` for the item id, torsion with colimits,
  `torsionDiagram`, `torsionColimit`, `integerTorsion`, `integerKernel`, and proposed full
  names. The item-id `grep -rn` in WeilConjectures returned no result. The names in
  `dag/lean_names_upstream.json` had no proposed-name collision.
- The relevant existing hit is
  `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`,
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`, read in full. It is restricted to
  `Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}` for a scheme T. Its helpers have the
  same restriction. It cannot express this node's arbitrary ringed sites or module
  sheaves. This delivery uses a general categorical construction for this node's own
  integer-kernel notion; it neither changes nor redefines that scheme-specific API.
- Local Mathlib source searches identified the existing `kernel.lift`, `HasKernels`,
  kernel-preservation API, `ColimitCocone`, module-sheaf limits and colimits, and the
  adjunction class. These are used directly instead of private copies.

Validation: scompile.py compiled the module as both an isolated sandbox module and its
actual library module without errors or warnings. An initial cocone-naturality mismatch
was repaired by stating the named inclusion law with its explicit identity composite on
the right; this is the natural-transformation convention, not a changed mathematical law.
No statement correction, disputed statement, or dependency defect was found.

## Second reading by NG

A separate pass by this dispatcher worker compared the unchanged node and the final
module, clause by clause. No second agent was started, as instructed; the maintainer's
independent review remains separate from this self-check.

The site, smallness, sheafification, coefficient, additive, kernel-preserving,
fully-faithful, and right-adjoint hypotheses all occur explicitly. `ringedSiteModules`
is the dependency abbreviation, and the torsion conclusion uses `toSheaf` on both
sides. The diagram uses every positive integer with divisibility, with actual kernel
lifts as its maps. Each helper theorem states a law in node proof step 1 and is named
in the Lean record. `alpha` is fixed by the kernel-inclusion equation; its naturality
is part of being a natural isomorphism. `theta` is fixed by every colimit leg and
satisfies the canonical-map equation in the correct direction. Colimit existence is
asserted in the conclusion, not assumed. All colimit choices are included; this
is the choice-independent version of the node's chosen-colimit statement.

The only change during this reading was the explicit identity in the cocone
naturality law required by Lean. No hypothesis, conclusion, node text, or dependency
record changed. All four definitions have real data and every theorem proof is `sorry`.
