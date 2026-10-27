## Worker report

The module `Sheaf.CategoryTheory.PresheafBarResolution` states
`CategoryTheory.PresheafBar.exists_resolution`. Its conclusion is the simultaneous
existence of a fully normalized `PresheafBar.Resolution`. This record expands the
node's construction and all its laws. The direct sums, generator inclusions,
restrictions, coefficient maps, faces, alternating differentials, augmentation,
identity insertion and coefficient-preserving comparison are actual definitions.
The record identifies the cochain complexes with those concrete terms and maps;
no definition chooses a resolution, map or isomorphism from the postponed theorem.
There is exactly one `sorry`, the whole proof of `exists_resolution`, whose
docstring gives the node's seven proof steps.

Source read: `literature/stacks-project/sites-cohomology.tex`, lines 10016--10116,
Tags 08PF and 08PG. In particular the displayed degree-two boundary has signs
`+,-,+`, first deletes the leftmost vertex, and last restricts the coefficient.
The DAG explicitly expands the presheaf resolution and omitted verifications.
The mathematical statement is unchanged. The only extra statement dependency is
the already landed definition owner `def-trf-derived-colimit-bar-system`, for its
existing `CategoryTheory.categoryBarDelete`; its theorem is not invoked.

Hypothesis and clause correspondence:

- Size convention: `E : Type u`, `[SmallCategory E]`, `R : Type r`, `[CommRing R]`.
  The module-value universe is `max u v`, so all the small chain and arrow sums
  fit, with independent coefficient-ring and upper module universes. There is no
  finiteness, nonemptiness, terminal-object, flatness or projectivity hypothesis.
- The category A is exactly the node's displayed functor category:
  `Presheaves.{u,v} E R = Eᵒᵖ ⥤ ModuleCat.{max u v} R`. The identity-cover topology
  is the bottom Grothendieck topology; no extra sheaf condition is imposed.
  `RingedSiteModules` and `SiteCoveringAxioms` retain the dependency conventions.
- `L_U(M)(V)` is the actual direct sum `freeTerm U V M`; `freeι` is its arrow
  summand. `freeRestriction` sends that summand to the one indexed by `b ≫ a`.
  `Resolution.L`, `freeIso`, `free_restriction`, `free_map` and `L_additive`
  express the functorial presheaf realization of exactly this formula.
- Chains are Mathlib's `ComposableArrows E n`: their left vertex is U_n and
  right vertex is U_0. `term F n V` sums F(U_0) over `(c,a : V → c.left)`.
  `termIso` identifies it with B(F)^(-n)(V). To make the presheaf-level sum
  explicit, `summand`, `summand_eq` and `summands_isColimit` give the normalized
  inclusions of L_(U_n)(F(U_0)) and their coproduct universal property.
- `colimitTerm F n` is the actual sum of F(U_0) over chains c; `colimitTermIso`
  identifies it with K(F)^(-n). `positive_zero` says both complexes vanish in
  every strictly positive integer degree, using the standard categorical zero
  property rather than an arbitrary choice of zero-object representative.
- All complexes are Mathlib `CochainComplex ... ℤ`, with the quasi-isomorphism
  notion of `def-weil-abstract-derived-category`.
- `restriction` changes only the incoming arrow; `restriction_eq` transports this
  rule to B. `termMap` and `colimitTermMap` apply `t.app (op c.right)` to x;
  `map_eq` and `colimit_map_eq` fix B and K on all coefficient morphisms.
- The vertex deletion is the existing `categoryBarDelete`. `deleteLeft` is the
  connecting arrow from the old left vertex to the new left vertex, and
  `deleteRight` is the arrow from the new right vertex to the old right vertex.
  Consequently `face` composes a with the first arrow for the first face,
  composes adjacent arrows internally, and restricts the coefficient for the
  last face. At the other faces `deleteRight` is an identity. `colimitFace`
  omits only the incoming arrow. These use F.map directly, so they also apply
  when the ring and module universes differ from the category's universe; the
  older same-universe `categoryBarFaceCoefficient` is not imposed as a restriction.
- `faces` and `colimitFaces` are natural transformations between degree functors;
  the former take values in presheaves. Thus the faces are presheaf maps and
  natural in F. `face_eq` and `colimit_face_eq` fix their complete formulas.
- `face_identity` is `face (n+1) j.succ ≫ face n i =
  face (n+1) i.castSucc ≫ face n j` for i ≤ j. Renaming j+1 to j gives exactly
  d_i d_j = d_(j-1) d_i for i < j. The K relation is stated as well.
- `differential` and `colimitDifferential` are `∑ j, (-1 : ℤ)^j.val • face_j`.
  The two `differential_eq` fields identify these with the cochain differentials
  from -(n+1) to -n, for every natural n. Complex structures supply d² = 0.
- `a` is a natural morphism B → F[0], using `HomologicalComplex.single` at zero.
  `augmentation_eq`, after the standard single-degree identification, is exactly
  the actual map `augmentation F V`, whose arrow summand acts by F(a).
- `contraction` is defined on every `(a,c)` summand by the chain `c.precomp a`,
  with incoming arrow `𝟙 V`. `augmentedContraction` is the identity summand at V.
  These have no V-naturality condition. `contraction_augmented` is a_F s_(-1)=1;
  `contraction_zero` is d s_0 + s_(-1) a_F=1; `contraction_succ` is
  d s_(n+1) + s_n d=1, in Lean's left-to-right composition convention.
- `quasiIso` asserts `QuasiIso (a.app F)` for every F in the presheaf category.
- `B_additive` and `K_additive` give additivity. `B_shortExact` and `K_shortExact`
  take a short complex S whose evaluation at every V is `ShortExact`, and assert
  `(S.map B).ShortExact` and `(S.map K).ShortExact`. These are short exact
  sequences of complexes, not merely a homology consequence.
- `C` is exactly Mathlib's chosen `colim` functor. `b` is a natural isomorphism
  of cochain complexes `B ⋙ C.mapHomologicalComplex (.up ℤ) ≅ K`, not a mere
  collection of cohomology isomorphisms.
- `comparison` forgets a and keeps `(c,x)` exactly. `comparison_eq` normalizes
  every component of b on every evaluated summand, and therefore determines b.
  `colimitAugmentation` sends the c-summand in degree zero to
  `colimit.ι F (op c.right)`. `colimit_augmentation_eq` identifies its composite
  with b^0 with C(a_F^0), including the canonical F[0]^0 ≅ F identification.

Dependency declarations read and used:

- `def-weil-size-convention`: its recorded metatheoretic convention, rendered
  by the explicit universes above; it deliberately has no declaration to import.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`, and the exact Mathlib
  `SheafOfModules` match. The node explicitly identifies these coefficients
  with the ordinary constant-ring presheaf category used here.
- `def-weil-pbc-sites-and-cohomology`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`,
  `Sheaf.CategoryTheory.SiteCoveringAxioms`; its source and identity-cover
  specialization were read. All sheaves on this topology are presheaves.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; its cochain and QuasiIso
  infrastructure supplies the complexes and quasi-isomorphism assertion.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, `colimit.ι`, `colimit.desc`, in
  `Mathlib.CategoryTheory.Limits.HasLimits`. `C = colim` uses that same choice.
- Added existing definition owner `def-trf-derived-colimit-bar-system`:
  `CategoryTheory.categoryBarDelete`, `Sheaf.CategoryTheory.DerivedColimitBar`.
  Its full signature and docstring were read; no copy of this notion remains.
  The model/system records are not assumed, and their existence theorem is not
  used. This same source module also contains the downstream parent theorem;
  a future proof import of this module into that parent must be omitted to avoid
  a module cycle, as stage 2 rule 7 prescribes. There is no DAG dependency cycle:
  this item cites only the definition node, not the parent statement node.
- Proof leaf `lem-weil-pbc-site-module-presheaf-sheafification-exact` has no
  `lean` record and needs none. Its exact Mathlib matches were read:
  `Abelian.functorCategoryAbelian`, evaluation preservation of limits and
  colimits (`Limits.FunctorCategory.Basic`), `sheafIsAbelian`,
  `presheafToSheaf`, and `ShortComplex.mapHomologyIso`. The proof uses clause (1),
  not a fresh site-exactness axiom. The proof imports expose the corresponding
  infrastructure; `HomologicalComplex.quasiIso_iff_evaluation` is also available.

Edge cases checked against the concrete formulas and record:

- Empty E: every K-term is an empty direct sum, there are no evaluated B terms,
  and C is the zero colimit. No `Nonempty E` assumption appears.
- One object with only identity: in degree one the two faces agree, so the
  alternating differential is zero; in degree two the three faces sum to the
  identity. The unnormalized bar complex and insertion identities hold.
- n=0: augmentation acts by F(a); s_(-1) uses `(V,𝟙 V,x)`; the two faces of
  the inserted degree-one chain give `(a,x) - (𝟙 V,F(a)x)`, exactly the
  `contraction_zero` identity.
- n=1 and the adjacent endpoint faces: composing two arrows agrees with
  restricting F twice. Nonadjacent deletion preserves x; the terminal deletion
  applies the sole coefficient restriction. Repeated identity arrows remain
  present, as required for the unnormalized resolution.
- Zero coefficient modules and the zero ring are included. No freeness or
  flatness of F(U_0) is used for exactness; finite-support lifts suffice.
- All natural n and positive integer cochain degrees are covered. There is no
  boundedness assumption on F, no equality of independent universes, and no
  assertion that the evaluation contraction is natural in V.

Searches made (all launcher searches use group Q83 and this item):

- `msearch.py leanfinder`: "Augmented bar resolution of a presheaf of modules
  on a small category contracts after evaluation". Eight hits, principally
  `classifyingSpaceUniversalCover` and `Rep.barResolution`; these concern group
  representations and do not give the arbitrary-category variable-coefficient
  presheaf resolution.
- `msearch.py loogle`: "CategoryTheory.SimplicialObject, DirectSum". Zero hits.
- `msearch.py grep`: `simplicialReplacement|barConstruction|barResolution|leftAdjointEvaluation`
  in `CategoryTheory`. Zero hits.
- `msearch.py leansearch`: "The augmented bar complex of a presheaf of modules
  on a category has a contracting homotopy after evaluation". Eight hits:
  generic augmentation constructors, short-complex homotopies, and
  `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`. None constructs this
  resolution with its coefficient and colimit normalizations.
- `msearch.py grep`: `freeYoneda|copower|leftAdjointEvaluation` in
  `Algebra/Category/ModuleCat`. Ten returned hits are free-Yoneda constructions
  for presheaves of modules over a ring presheaf, including the cyclic
  coefficient module R; they do not give L_U(M) for arbitrary M or the bar result.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for bar-resolution,
  augmented-bar, simplicial replacement and evaluation-adjoint names. No
  upstream module carries this item; the requested literal item-id search in
  `lean/WeilConjectures` also found none. Project hits included group bars,
  condensed internal bars, and `DerivedColimitBar`.
- Further `rg` for `freeRepresentable`, `freeAt`, `freePresheaf` and L_U:
  the site's free representable has coefficients R(V) and is sheafified, not
  arbitrary M. The specialized Cech free presheaf is also a different object.
  The full `DerivedColimitBar` definitions were then read. They prescribe K
  inside a derived-model record, but not the evaluated B generator formulas,
  contraction or B short exactness of this node. Their deletion notion was
  reusable and is now reused through its actual definition owner.
- DAG search and `tools/blueprint_refs.py search 'presheaf bar'`: no blueprint
  node match. Reading the nearby bar nodes found
  `def-trf-derived-colimit-bar-system`; this existing node is cited rather than
  creating another definition owner. No new independent notion/node is needed:
  the auxiliary declarations only expand formulas already in this item's own
  statement.

Validation: the final module compiled in module mode under both the sandbox and
actual library module names using the prescribed `scompile.py`; 8.6 s and 6.5 s.
No compiler errors or warnings were emitted. No local Lean invocation or global
build was run. No statement dispute or correction is needed.

## Second reading by Q83

Author's separate clause check, under the dispatcher's direct-delivery workflow;
the maintainer supplies the independent review. I reopened the unchanged node and
the complete module and checked the binders, all generator maps, both complexes,
face identities, the augmented endpoint identities, quasi-isomorphism, both
short-exactness assertions, naturality of b, and its degree-zero normalization.
The first draft duplicated the already published vertex-deletion definition;
I removed that definition and imported its existing owner. The first draft
expressed the L-term coproduct only through flattened evaluated direct sums;
I added normalized presheaf summand inclusions and `summands_isColimit`, so the
presheaf coproduct clause itself is explicit. I checked the Lean composition
order in all three contraction identities and in the last normalization equation.
I verified that s is only a raw map at fixed V, that no nonempty-category condition
was added, and that the theorem does not assume a bar system or choose data from
an unproved theorem. The added definition dependency is definition-only at the
DAG level and cannot close the parent theorem's proof dependency cycle.
