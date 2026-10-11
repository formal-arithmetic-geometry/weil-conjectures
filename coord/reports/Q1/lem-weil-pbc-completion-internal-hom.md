## Worker report

The module `Sheaf.AlgebraicGeometry.CompletionInternalHom` states
`AlgebraicGeometry.completion_internal_hom_bijective`, with its only proof `sorry`.
It states the canonical comparison, including the construction clauses of the node,
without introducing another definition of completion, coherent modules, or internal Hom.
The existential maps are completely specified by quotient factorization and component
equalities; this is not merely the existence of an arbitrary bijection.

Source checked: [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882),
Lemma 30.23.5 and its affine-local proof. The local literature checkout is absent on this
machine, so the official online statement and proof were read instead. The source's
proof interchanges its letters M and N; the declaration consistently uses Hom(G,F).
The declaration docstring gives all five steps of the DAG proof and names their inputs.

Hypotheses and clauses, in node order:

- Noetherian scheme X: `{X : Scheme.{u}} [IsNoetherian X]`.
- Quasi-coherent ideal sheaf I: `I : X.IdealSheafData`, the shared scheme ideal-sheaf data.
- Coherent F and G: `F G : CoherentModules X`, the full subcategory defined by
  `RingedSpace.IsCoherent X.toRingedSpace`. No properness, affine hypothesis, or condition
  on I is imposed.
- H = internal Hom(G,F): every occurrence is
  `SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G.obj F.obj`.
  The coefficient sheaf is explicit because Lean cannot reconstruct a commutative-ring
  sheaf from its image under the forgetful functor.
- I^n M and M/I^n M: `Scheme.idealSheafPower`, `Scheme.idealModuleProductι`, and
  `formalModuleQuotient`. The projection pi_n is `formalModuleQuotientπ`.
- Positive levels only: n : N in the first clauses represents exponent n+1; n : N^op
  in the remaining clauses represents exponent n.unop+1. Every integer exponent >=1
  occurs, and no exponent-zero condition is imposed.
- Postcomposition H -> Hom(G,F_n) vanishes on I^n H: the first conjunction states the
  product inclusion composed with `homObjMap (identity G) pi_n` equals zero.
- Every local map G -> F_n vanishes on I^n G and factors uniquely through G_n:
  the second conjunction states `IsIso (homObjMap qG_n (identity F_n))`. An isomorphism
  of Hom sheaves asserts the unique factorization on every localized open, not just
  on global sections.
- The maps e_n : H_n -> Hom(G_n,F_n) are quantified in `e`. Their factorization equation
  is `qH_n ≫ e n ≫ homObjMap qG_n (identity F_n) = homObjMap (identity G) qF_n`.
  Since qH_n is a cokernel projection and precomposition by qG_n is an isomorphism,
  this specifies exactly the maps induced by postcomposition and both quotients.
  Taking `sectionsMap (e n)` and `homObjSectionsEquiv G_n F_n` gives epsilon_n.
- Compatibility with quotient transitions and reduction of maps: for every a -> b in
  N^op, the third equation compares e_a followed by postcomposition with F_a -> F_b
  against H_a -> H_b followed by e_b and precomposition with G_a -> G_b.
  This equality in Hom(G_a,F_b) is exactly the reduction square, stated without
  introducing a second definition of the reduction operation rho.
- The inverse limit of global sections is the subtype of families s_n in H_n.sections
  satisfying `sectionsMap (formalCompletionSystem ... .map f) (s a) = s b` for each
  transition f. Mathlib `sections` is a compatible section on all opens, equivalently
  a section on the terminal open X. Conditions for all transitions are equivalent
  to adjacent transition conditions by composition, so no extra constraint is added.
- The resulting completion morphism is `Φ s`, with codomain
  `(completion X I).obj G ⟶ (completion X I).obj F` in Coh(X,I).
  The equation `(Φ s).hom.app n = homObjSectionsEquiv ... (sectionsMap (e n) (s.val n))`
  identifies every component with epsilon_n(s_n). Being a morphism of the full
  subcategory means these components form a natural transformation, precisely the
  compatible family required in the node.
- The last clause `Function.Bijective Φ` is the node's bijectivity conclusion for that
  prescribed map. Neither an arbitrary equivalence nor an unconnected comparison
  function is substituted.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentModules`,
  `formalModuleQuotient`, `formalModuleQuotientπ`, `formalCompletionSystem`,
  `CoherentFormalModule`, and `completion` (def-weil-pbc-coherent-formal-module).
- `Sheaf.AlgebraicGeometry.Coherent` (imported through the preceding module):
  `AlgebraicGeometry.RingedSpace.IsCoherent` (pqf-def-coherent).
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`, and `homObjSectionsEquiv`
  (def-pur-sheaf-hom). The full signatures and docstrings were read in the source.
- Mathlib's `SheafOfModules.sections`, `sectionsMap`, and the full-subcategory
  morphism projection `.hom` provide sections and component notation.

Edge cases checked before writing: the empty scheme is allowed; zero F or G are allowed;
I=0 gives constant systems, and I=O_X gives zero quotients and singleton source and target;
no adic separatedness or completeness of X or F is assumed. Positive level 1 is included.
The universe u is explicit, all indices and quantified variables are bound, and internal
Hom on the open site remains in the same module universe. No characteristic assumption
is introduced. No statement correction, disputed statement, new node, or unusable
recorded dependency was found.

Searches for an existing statement (2026-10-11):

- msearch.py LeanFinder: "Morphisms between completions of coherent sheaves are inverse
  limit of global sections of internal Hom modulo ideal powers". Eight hits, including
  presheaf module limit constructions and Hausdorffification; none states this theorem.
- msearch.py Loogle: "SheafOfModules.homObj, AdicCompletion.map". Zero hits; homObj is
  unknown to that Mathlib service (it is an existing project declaration, used here).
- msearch.py grep: "completion.*[Hh]om|[Hh]om.*completion" over Mathlib. Twenty-five hits,
  on ring homomorphisms and unrelated completions, none on coherent sheaf Hom.
- msearch.py LeanSearch: "completion coherent sheaf internal Hom inverse limit sections".
  Service unavailable (Internal Server Error); recorded as unavailable, no verdict.
- rg of the source WeilConjectures tree and lean/Sheaf for
  "completion.*[Hh]om|[Hh]om.*completion|lem-weil-pbc-completion-internal-hom": no source
  match and only unrelated completion/ring-hom comments in four landed modules.
- `tools/lean_names_upstream.py show lem-weil-pbc-completion-internal-hom` gave no matching
  declaration. A further rg for `completion_internal_hom_bijective` in the upstream
  name index, Mathlib, WeilConjectures, and lean/Sheaf found none.

Validation: scompile.py on the server compiled the final module cleanly in 2.6 seconds,
with no errors or warnings. No Lean compilation was attempted locally. Delivery dry run
is run after recording the node's exact signature. The independent second reader has
not yet reviewed this file and will write the second-reading section and deliver.

## Second reading by Q1

I independently read the item's JSON and CompletionInternalHom.lean, all three
statement-dependency nodes and their recorded modules. I also fetched and read the
Stacks coherent.tex source (official stacks/stacks-project repository): Section
0EHN at lines 6246–6279, the completion functor at 6407–6420, and
lemma-completion-internal-hom, Tag 0882, at 6437–6471. The section assumes precisely
Noetherian X and a quasi-coherent ideal; neither properness nor an adic completeness
hypothesis is implicit. The online Tag 0882 and 0EHN pages agree with the TeX.
The proof's M/N reversal is a lettering error; the node and Lean consistently use
Hom(G,F). No correction of the node is needed.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Noetherian scheme X: `{X : Scheme.{u}} [IsNoetherian X]`. Matches; the universe
   is bound and no affine, separated, proper, or base-field hypothesis is added.
2. Quasi-coherent ideal I contained in O_X: `(I : X.IdealSheafData)`. Matches.
   I opened Mathlib's IdealSheafData fields: ideals on affine opens with localization
   compatibility, not an arbitrary submodule or ideal of global sections. Its
   shared `toModulesι` supplies the ideal inclusion used in every power/product.
3. Coherent F and G: `(F G : CoherentModules X)`. Matches. The recorded dependency
   defines this as the full subcategory using RingedSpace.IsCoherent. I opened that
   predicate: finite type plus finite-type kernels of all maps from finite free
   modules on every open. It is the dependency's Stacks coherence, rather than the
   upstream predicate quasi-coherent plus finite presentation.
4. H = sheaf Hom(G,F): `SheafOfModules.homObj
   (R := X.toRingedSpace.sheaf) G.obj F.obj`. Matches in both argument order and
   coefficient sheaf. I opened the source InternalHom module: its objects are
   linear maps on the localized site, not pointwise linear maps on sections.
   `homObjMap f g` is precomposition by f and postcomposition by g.
5. Powers, products, quotients, and pi_n: `Scheme.idealSheafPower`,
   `Scheme.idealModuleProductι`, `formalModuleQuotient`, and
   `formalModuleQuotientπ`. Matches. I opened the shared product/power definitions:
   multiplication-image product, first power I, successive products, and actual
   cokernel quotients. These are the dependency's constructions, not private copies.
6. Positive n only: every displayed level uses `n + 1` or `n.unop + 1`.
   Matches n >= 1 bijectively. `op 0` is level 1, not exponent zero.
7. Postcomposition kills I^n H: the first conjunct is precisely the composite
   product inclusion followed by `homObjMap (𝟙 G.obj) pi_n = 0`. Matches the node's
   sheaf-level annihilation assertion, not only annihilation of global sections.
8. Every local G -> F_n kills I^n G: the second conjunct says `IsIso` of
   `homObjMap qG_n (𝟙 F_n)`. Matches: quotient projections are cokernels, hence
   unique factorization identifies Hom(G_n,F_n) with Hom(G,F_n) on every open.
   This is exactly the local-map clause, with uniqueness already intrinsic to
   the quotient. It adds no condition on F or G.
9. Induced maps epsilon_n: `∃ e` supplies H_n -> Hom(G_n,F_n), and the first
   equation after it is `qH_n ≫ e n ≫ homObjMap qG_n (𝟙 F_n) =
   homObjMap (𝟙 G.obj) qF_n`. Matches. Since qH_n is epi and the precomposition
   map is iso, this equation determines e_n uniquely; an arbitrary bijection
   cannot satisfy the statement in place of the canonical map. Taking
   `sectionsMap (e n)` followed by `homObjSectionsEquiv` gives epsilon_n.
10. Compatibility with quotient transitions and reduction: the next equation
    compares `e a` followed by postcomposition by F_a -> F_b with H_a -> H_b
    followed by `e b` and precomposition by G_a -> G_b. Both land in
    Hom(G_a,F_b); it is exactly the reduction square. Quantification over all
    arrows of N^op is equivalent to adjacent compatibility, since the transitions
    form the recorded formalCompletionSystem functor. Matches.
11. Inverse limit of Gamma(X,H_n): the subtype in the domain of `∃ Φ` contains
    precisely families of H_n.sections satisfying every transition equation.
    Matches. Mathlib SheafOfModules.sections is a compatible section on all opens;
    the terminal open X identifies it with ordinary global sections. No sections
    on the formal scheme or sections of an unrelated module are substituted.
12. Compatible epsilon_n(s_n) define a morphism G^ -> F^: the codomain is
    `((completion X I).obj G ⟶ (completion X I).obj F)`. I opened completion,
    IsCoherentFormalModule and CoherentFormalModule: the objects are the positive
    quotient systems, and morphisms of this full subcategory are natural
    transformations. The equation `(Φ s).hom.app n = homObjSectionsEquiv ...
    (sectionsMap (e n) (s.val n))` prescribes every component as epsilon_n(s_n).
    Matches the node's construction and direction of the morphism.
13. The resulting map is bijective: `Function.Bijective Φ` applies to that same
    component-prescribed Φ. Matches, with e and Φ existentially introduced after
    the universal input objects; their equations determine them, so neither the
    conclusion nor the quantifier order is weakened.

Edge cases: X may be empty, and F or G may be zero; there is no nonempty/nonzero
binder. For I=0 the quotient systems are canonically constant and the comparison
is the internal-Hom global-sections identification. For I=O_X all positive
quotients vanish and both sides are singleton sets. An arbitrary characteristic
is allowed; no field occurs. The index is the fixed nonempty N^op, so the empty
index-set issue does not arise. n=0 is allowed as a Lean index and means exponent
1; the source has no exponent-zero condition. All opens, sheaves, modules, and
Hom objects use the scheme's explicit universe u, which can be raised for larger
objects; no independently smaller test-object universe or unbound universe occurs.

Independent searches, using different wording from the first worker:

- LeanFinder via msearch.py: "Adic formal coherent modules morphisms computed by
  completed sheaf of linear maps". Eight hits: AdicCompletion.map/of/lift and
  Hausdorffification/IsAdicComplete constructions. Their displayed signatures
  concern ring modules and completion of a given linear map, not this sheaf-Hom
  comparison. No existing statement of the node was found.
- Loogle via msearch.py: `"hom", "completion"`. Twelve returned hits concern
  Cauchy/uniform/group/ring completion homomorphisms; none is this statement.
- LeanSearch via msearch.py: "Morphisms of coherent adic systems equal compatible
  global sections of quotients of the sheaf of linear maps". Internal Server
  Error: unavailable, with no mathematical verdict inferred.
- Mathlib grep via msearch.py: `formal.*(hom|morph)|((hom|morph).*adic)`.
  Returned formal-unramified, p-adic and unrelated entries, no coherent formal
  internal-Hom theorem. A narrower direct rg over Mathlib AlgebraicGeometry and
  ModuleCat, the source WeilConjectures tree, and lean/Sheaf for
  `completion.*hom|hom.*completion|formal.*module` found the existing formal
  category dependency and unrelated ring-completion/derived/adic-coefficient
  modules; none states this comparison. Broad rg for the delivered declaration
  and Stacks label found no duplicate. Existing internal Hom, coherent modules,
  ideal products, quotient systems and completion are all used through their
  recorded dependencies, so no new definition is justified.

No mismatch was found and no mathematical signature, node statement, or Lean
source was changed. There are no new nodes or dependency modules in this delivery.
The single theorem has `sorry` as its entire proof, no definition or local notation
is introduced, both imports are used, and every line is at most 100 characters.
The module and theorem docstrings name Tag 0882 and the exact blueprint id; the
five numbered proof steps render the node's construction, affine reduction,
equivalence, completion/base-change calculation, and affine-local gluing, with
all relevant node inputs named. The node's lean.statement equals the theorem
signature after the required whitespace normalization.

Independent validation: scompile.py compiled this unchanged 108-line module on
the server in 2.2 seconds, exit code 0, with no errors or warnings. Second reading
changed only this report by appending the independent source/signature review.
