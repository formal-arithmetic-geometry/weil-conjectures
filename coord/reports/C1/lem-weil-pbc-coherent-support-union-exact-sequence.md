## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentSupportUnionExactSequence` states
`AlgebraicGeometry.Scheme.Modules.exists_coherent_submodule_of_support_union`, with
one theorem and its proof `sorry`. There are no new definitions, dependency modules,
or statement corrections.

Hypotheses and clauses, in the order of the node:

- A scheme X is `(X : Scheme.{u})`.
- Noetherian means `[IsLocallyNoetherian X] [CompactSpace X]`: locally Noetherian
  and quasi-compact underlying space, precisely the node's explicit convention.
- The coherent O_X-module is `(F : X.Modules)` with
  `hF : RingedSpace.IsCoherent X.toRingedSpace F`.
- The two closed subsets are `(Z Z' : Set X)` with `hZ : IsClosed Z` and
  `hZ' : IsClosed Z'`. They need not be disjoint, proper, or nonempty.
- The support equality is
  `hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = Z ∪ Z'`.
  A stalk is zero exactly when its additive-group carrier is subsingleton.
- The coherent submodule is represented by the existential object `G' : X.Modules`
  and inclusion `i : G' ⟶ F`, with `RingedSpace.IsCoherent X.toRingedSpace G'`.
  The `ShortExact` clause includes `Mono i`, so i indeed represents a submodule;
  this is the categorical description of a subsheaf, up to isomorphism over F.
- The quotient is explicitly `cokernel i`, with
  `RingedSpace.IsCoherent X.toRingedSpace (cokernel i)`.
- The requested short exact sequence is
  `(ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact`.
  This gives the monic inclusion, exactness at F, and epic canonical quotient map.
- The last two conjuncts give respectively the support of G' contained in Z' and
  the support of the canonical quotient contained in Z, using the same stalk locus.

Dependencies read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- def-weil-pbc-scheme-conventions: a convention record without its own declaration;
  quasi-compactness of a scheme is `CompactSpace X`.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.Coherent`,
  `AlgebraicGeometry.RingedSpace.IsCoherent`. Its full finite-type and kernel
  condition was read; for schemes its moduleRings carrier is X.Modules.
- def-weil-sheaf-of-modules-category:
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`, `AlgebraicGeometry.Scheme.Modules`,
  imported transitively through Coherent. The abelian structure supplies cokernels.
- def-weil-pbc-closed-subset-proper-over-base:
  `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`,
  `Scheme.Modules.HasSupportProperOver` was read. Its note and docstring explicitly
  specify the inline support locus used here. No properness notion is needed here,
  so that module is not imported just to obtain its support convention.
- def-weil-pbc-module-stalk:
  `Sheaf.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor` and all its declarations were read.
  The stalk carrier is Mathlib's `TopCat.Presheaf.stalk`, imported through
  `Mathlib.Algebra.Category.ModuleCat.Stalk`. No stalk map or bundled stalk
  functor is needed, and no alternative stalk is defined.
- The canonical quotient and exactness use Mathlib `cokernel`, `cokernel.π`,
  `cokernel.condition`, and `ShortComplex.ShortExact`.

Source checked: the local literature file is not present on this machine, so the
complete statement and proof were read at https://stacks.math.columbia.edu/tag/01YD
(Lemma 30.12.1). They agree with the node. The docstring carries all seven DAG proof
steps and their dependency identifiers, including the power-zero case.

Edge cases checked mathematically before writing: the empty scheme has no stalks
and admits the zero sequence; F = 0 forces Z and Z' empty and again admits that
sequence; Z empty admits G' = F, quotient zero; Z' empty admits G' = 0, quotient F;
Z = Z' and overlapping subsets are allowed. No positive dimension, characteristic,
nonemptiness, disjointness, affine, or separated hypothesis has been introduced.
One explicit universe u follows the scheme's universe for its module category and
stalks, and all binders are explicit. No STATEMENT-DISPUTED or node fault was found.

Searches for an existing statement (msearch calls used group C1 and this item):

- LeanFinder: `coherent sheaf support union two closed subsets short exact sequence`.
  Eight hits: ideal-sheaf support suprema/intersections, zero loci and gluing-image
  results; none asserts the coherent subsheaf and quotient existence here.
- Loogle: `"support", "exact"`. Four hits: three supported homological-complex
  exactness lemmas, and `Module.support_of_exact` for modules over a ring.
  None supplies the scheme-sheaf decomposition statement.
- msearch grep: `support.*exact|coherent.*support`, subdirectory AlgebraicGeometry:
  zero hits.
- LeanSearch: `coherent module support union closed subsets short exact sequence`:
  service unavailable, Internal Server Error; no verdict inferred from this search.
- rg of `support.*union|supportUnion|support_union` in WeilConjectures and lean/Sheaf:
  unrelated ideal-support and polynomial hits; the landed
  CoherentFiltrationIntegralSubschemes docstring cites this item, but does not state it.
- rg of this node id in WeilConjectures: no hits.
- rg of `exists_coherent_submodule_of_support_union|CoherentSupportUnionExactSequence`
  in dag/lean_names_upstream.json, WeilConjectures, all Mathlib and lean/Sheaf:
  no hits; the chosen declaration name is available.

Validation: scompile.py compiled this module on the server in 1.9 seconds with
exit code 0 and no warnings. The delivery dry run is the final validation; the
independent second reader supplies their own section and delivers.

## Second reading by C1

I independently read the item node, its seven proof steps, every statement dependency
node and the dependency declaration bodies. No statement correction, new definition
node, or dependency module is present or required. No mismatch was found; the Lean
module and node record are unchanged. This section records the independent reading.

Source: the local Stacks .tex is absent. I read the actual coherent.tex source at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
section-devissage, lemma-prepare-filter-support and its proof, and checked Tag 01YD
at https://stacks.math.columbia.edu/tag/01YD. The section assumes a Noetherian scheme;
its introductory coherent/subquotient facts add no hypotheses. No separatedness,
base field, or characteristic restriction is assumed.

The node's objects, hypotheses and conclusions, matched item by item:

1. X is an arbitrary scheme: `(X : Scheme.{u})`. PASS. Mathlib's Scheme extends
   LocallyRingedSpace with local affine charts over arbitrary commutative rings.
2. X is Noetherian, explicitly locally Noetherian and quasi-compact in this node:
   `[IsLocallyNoetherian X] [CompactSpace X]`. PASS. The former's component_noetherian
   field quantifies over affine opens, equivalent to the dependency's affine-cover
   formulation. CompactSpace means quasi-compactness, without Hausdorffness.
3. F is an O_X-module: `(F : X.Modules)`. PASS. Scheme.Modules is
   `SheafOfModules.{u} X.ringCatSheaf`, with its abelian category instance; no
   additional abelian-category or cokernel-existence hypothesis is introduced.
4. F is coherent: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. PASS.
   The dependency definition requires finite type and finite-type kernels of every
   map from a finite free module on every open, exactly the node's notion. Its
   moduleRings carrier agrees with X.Modules; there is no substitute predicate.
5. Z and Z' are closed subsets of X: `(Z Z' : Set X) (hZ : IsClosed Z)
   (hZ' : IsClosed Z')`. PASS. No disjointness, properness or nonemptiness is assumed.
6. Supp F = Z union Z': `hSupp : {x : X | ¬ Subsingleton
   (F.presheaf.stalk x)} = Z ∪ Z'`. PASS. Scheme.Modules.presheaf is the underlying
   additive-group presheaf. Mathlib Stalk supplies precisely its colimit stalk and
   stalk-ring module structure. PresheafOfModules.stalkObj in the recorded stalk
   dependency bundles that same carrier, not a different stalk. Subsingleton is
   equivalent to vanishing for an additive-group stalk. The inline locus agrees
   verbatim with HasSupportProperOver's support convention; that unrelated
   properness predicate need not be imported or assumed.
7. There exists a coherent submodule G' of F: `∃ (G' : X.Modules) (i : G' ⟶ F)`
   and `RingedSpace.IsCoherent X.toRingedSpace G'`, with monicity contained in
   `(ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact`. PASS.
   I opened ShortComplex.ShortExact: its fields are exact, Mono of its first map,
   and Epi of its second. A monic module-sheaf map represents the subsheaf up to
   isomorphism over F, preserving precisely the node's submodule meaning.
8. The quotient F/G' is the cokernel of that inclusion and is coherent:
   `RingedSpace.IsCoherent X.toRingedSpace (cokernel i)`. PASS. The same i is used
   throughout; the canonical cokernel is an allowed representative of the quotient.
9. The sequence is short exact: the ShortExact clause in item 7 uses i and
   `cokernel.π i`. PASS. It asserts all three exact-sequence requirements and no
   splitness. The displayed zero-composition proof is constructor data, not an
   extra conclusion or hypothesis.
10. Supp G' is contained in Z': `{x : X | ¬ Subsingleton
    (G'.presheaf.stalk x)} ⊆ Z'`. PASS.
11. Supp(F/G') is contained in Z: `{x : X | ¬ Subsingleton
    ((cokernel i).presheaf.stalk x)} ⊆ Z`. PASS. The order of Z' and Z is correct;
    both are inclusions, with neither unjustified equality nor omitted clause.

Edge cases: the empty scheme has no support points and allows the zero sequence.
For F = 0 the support equality forces both closed subsets empty. If Z is empty,
G' = F and the quotient is zero; if Z' is empty, G' = 0 and the quotient is F.
Overlaps, Z = Z', and Z or Z' = X remain allowed. No index type occurs. The power
n is only in the proof docstring, which explicitly covers n = 0 and the identity
sequence. No dimension, characteristic or field condition occurs. Universe u is
explicitly bound and arbitrary; the sheaves and stalks use the dependency's
Scheme.Modules universe convention, with no free variable or extraneous instance.

Independent searches (queries different from the first reader's):

- LeanFinder via msearch: `Noetherian scheme coherent sheaf decomposition into
  subsheaf and quotient with prescribed closed supports`: eight hits, on sections
  vanishing on basic opens, ideal-sheaf constructors/comparison, and finite affine
  Noetherian covers. None states this decomposition existence.
- Loogle via msearch: `"support", "cokernel"`: zero hits.
- LeanSearch via msearch: `Noetherian scheme coherent subsheaf quotient supported
  on complementary closed pieces`: unavailable (Internal Server Error). No
  absence verdict is inferred from that unavailable service.
- rg in Mathlib AlgebraicGeometry, WeilConjectures and the project's lean/Sheaf:
  `support.{0,50}(decompos|split|union)|(?:subsheaf|submodule).{0,50}support`.
  Hits concern polynomial supports, ideal supports, finite-support approximation,
  and other constructions. CoherentFiltrationIntegralSubschemes cites this lemma
  in its docstring but states a finite filtration, not this two-piece splitting;
  I opened its statement to check this.
- rg across all Mathlib: `support.*exact|support.*cokernel|coherent.*support`.
  I opened Module.support_of_exact in RingTheory/Support. It deduces a support
  equality from an already given exact sequence of modules over a ring, whereas
  this item constructs a sequence of module sheaves on a scheme; it is no match.
- rg of the proposed full-name suffix and module name in dag/lean_names_upstream,
  all Mathlib, WeilConjectures and lean/Sheaf found no declaration collision.

H5/H6/H8/H9: no new definitions or hollow data; the one theorem's proof is sorry.
Both docstrings carry the source and blueprint id. The theorem docstring follows
all seven DAG proof steps with their cited dependencies, including coherence,
stalk exactness, quotient support, annihilation on X minus Z', restriction of
ideal products, and the final choice. All lines are at most 100 characters;
imports supply coherence, Noetherian hypotheses, stalks, and ShortExact. No
file-local notation, private definition or unbound universe/variable occurs.
The node's lean.statement is verbatim the file's signature before `:= by`.

Validation: independent scompile.py invocation with the absolute sandbox module
path compiled cleanly in 1.9 seconds, exit code 0 and no warnings. The initial
relative-path invocation could not find the sandbox file; rerunning with its
absolute path resolved that invocation issue without changing any tool or source.
