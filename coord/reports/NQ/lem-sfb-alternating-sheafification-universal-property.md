## Worker report

The item is stated as `PresheafOfModules.alternating_sheafification_universal_property`
in `Sheaf.Algebra.Category.ModuleCat.Sheaf.AlternatingSheafificationUniversalProperty`.
Its proof is `sorry`. The original natural-language statement and proof are unchanged;
`stmt_deps` gains the two definitions below. There are no dependency repairs and no
statement correction or disputed assertion.

The source was read in Stacks `sites-modules.tex`, the complete lemma
`lemma-sheafification-presheaf-modules` (03CY) and the following adjunction discussion.
03CY states linear extension, not this finite-variable theorem. The finite-product
argument is the six-step argument already recorded in the item; all six steps appear
in the theorem docstring, with 00WH/00WJ and 00DM and the corresponding dependency ids.

Hypotheses and clauses, matched individually:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  Its object and morphism universes are independent. Rings and modules live in
  `max u v w`, which contains the chosen small site and permits any larger coefficient
  universe. The size convention allows using a small skeleton. Neither a topology nor
  a scheme is specialized. `HasWeakSheafify` and `WEqualsLocallyBijective` are the
  Mathlib module-sheafification interface; in these size bounds their hypotheses are
  supplied by ordinary concrete sheafification, rather than extra mathematical
  restrictions on the site.
- `A : Cᵒᵖ ⥤ CommRingCat` is the arbitrary presheaf of commutative rings.
  `B : Sheaf J CommRingCat` is its associated sheaf, presented by `α`, locally injective
  and locally surjective. A locally bijective map from a ring presheaf to a ring sheaf
  presents its sheafification (03CY and the recorded Mathlib interface). This is an
  arbitrary presentation of the associated sheaf, not a free choice of coefficient
  map: the two local bijectivity hypotheses are essential. Ring homomorphisms between
  these commutative rings are exactly the commutative-ring homomorphisms after forgetting.
  Taking the canonical ring sheafification and its unit gives the node literally.
- `P : PresheafOfModules (A ⋙ forget₂ CommRingCat RingCat)` carries exactly the
  sectionwise A-module structures and semilinear restrictions of the node.
  The equivalences are quantified over every such P, so the theorem also states the
  requested naturality in P without fixing a special presheaf.
- `(sheafification α).obj P` is P-sharp, with Mathlib's induced B-module structure.
  It has abelian sheafification as its underlying sheaf by
  `PresheafOfModules.sheafificationCompToSheaf`.
- `n : ℕ` includes zero and has no positivity, rank, freeness or characteristic bound.
- `SheafOfModules.siteExteriorPower ((sheafification α).obj P) n` is exactly the
  sheafification of the existing presheaf `U ↦ ⋀[B(U)]^n P-sharp(U)`.
  No iterated tensor or abstract representing object replaces the stated exterior power.
- `F : ringedSiteModules ...` is any B-module sheaf, using the dependency's abbreviation
  of Mathlib's `SheafOfModules`. The Hom on the left is the category's actual linear
  sheaf morphism type.
- `SiteAlternatingFamily P ((restrictScalars α).obj F.val) n` is exactly the right side.
  Its underlying data are `∀ U, AlternatingMap (A.obj U) (P.obj U) (...) (Fin n)`.
  Mathlib's `AlternatingMap` means multilinear and zero on tuples with repeated entries;
  it is stronger than merely a sign rule in characteristic two, as required here.
  Its subtype property quantifies over every `U V`, arrow `U ⟶ V` of the opposite site,
  and tuple, and is precisely compatibility with every restriction. `restrictScalars α`
  gives the specified A(U)-action on F(U), not an unrelated module structure.
- The conclusion supplies a family of actual `Equiv`s. Each includes both inverse laws,
  so the conclusion is bijectivity, rather than just existence of an extension or a
  bare equivalence with unspecified evaluation.
- The first conjunct fixes each equivalence on every h, U and tuple x by
  `h.val.app U (siteExteriorWedge ... (fun i ↦ unit.app P.app U (x i)))`.
  `unit` is the actual `sheafificationAdjunction α` unit. `siteExteriorWedge` takes the
  sectionwise wedge and then the exterior presheaf's sheafification unit. Thus this is
  exactly the displayed evaluation formula in the node.
- The second conjunct states naturality in F, pointwise on every tuple:
  evaluation of `h ≫ v` equals `v.val.app U` applied to evaluation of h, for every v.
- The third conjunct states naturality in P, again pointwise on every tuple and for
  every `g : P' ⟶ P`: evaluation after `siteExteriorHom ((sheafification α).map g) n`
  equals the original family on `g.app U ∘ x`. This is the actual sheafified exterior
  map, constructed from sectionwise `exteriorPower.map`, not an arbitrary map satisfying
  an added hypothesis. Equality on every U and tuple is equality of alternating families.
- For n = 0, `Fin 0 → P(U)` has one element, and all multilinearity and repeated-entry
  conditions are vacuous. Consequently the right side is a restriction-compatible
  family of elements of F(U). The exterior wedge is the empty wedge, namely 1 in the
  degree-zero exterior power. The displayed formula and both naturalities still apply.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings` describes
  the covering-site convention; its induced Grothendieck topology and Mathlib sheaves
  provide the topology interface used here. No choice of a special covering family is made.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; the latter is the underlying abelian universal property.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: `sheafification`,
  `sheafificationAdjunction`, `sheafificationCompToSheaf`, and the unit formula. This is
  exactly the `lem-pc-sites-module-sheafification-interface` Mathlib match and also the
  recorded presheaf-module sheafification definition used by the new nodes.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` and `ExteriorPower.Basic`:
  `ExteriorAlgebra`, `ExteriorAlgebra.ι`, `exteriorPower`, `ExteriorAlgebra.ιMulti`,
  `exteriorPower.ιMulti`, `exteriorPower.map`, and `alternatingMapLinearEquiv`.
  The last is the exact `lem-trf-exterior-power-universal-property` Mathlib leaf.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ExteriorPower`:
  `PresheafOfModules.exteriorPower` and `exteriorPower_map_ιMulti`. The complete source
  construction and its docstrings were read. Its canonical semilinear restrictions
  are reused, with matching coefficient/module universes; no presheaf is redefined.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, used directly for F
  and exterior sheaves. It abbreviates the genuine Mathlib category of module sheaves.
- The recorded tensor dependency
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly imported;
  the exterior construction does not replace that tensor. It uses the node's explicit
  sheafification-of-exterior-powers definition instead.
- The proof-only Mathlib imports are `Sites.PreservesSheafification`, exposing
  `sheafifyComposeIso` and its unit factorization (the underlying-set dependency), and
  `Sites.LeftExact`, exposing left exact set sheafification (the finite-limit dependency).
  The ordinary exterior universal property is already available through the public imports.
- `def-weil-size-convention` is metatheoretic and is rendered by the explicit universes.

Edge cases checked mathematically before stating: n = 0 (compatible elements and the unit
empty wedge); n = 1 (the ordinary module-sheafification adjunction); n = 2 in characteristic
2 (repeated entries still vanish); the zero module, including its nonzero degree-zero
exterior power; the zero coefficient ring; an empty site; the trivial and maximal
Grothendieck topologies; arbitrary module morphisms, without injectivity or freeness;
and distinct object/morphism universes. None is excluded by the signature. No rank or
nonempty-site assumptions were introduced. Auto-bound implicits are disabled in every file.

Searches for the item: `msearch.py` LeanFinder, query "Alternating multilinear maps from
module presheaves extend uniquely through sheafification represented by sheafified exterior
power", returned the single-variable sheafification Hom equivalences and ordinary exterior
universality, not this theorem. Loogle queries `"exteriorPower", "sheafification"` and
`"sheafification", "alternating"` both returned zero hits. Mathlib grep
`exteriorPower|alternating` under `Algebra/Category/ModuleCat` found only the ordinary module
exterior functor. `rg` of the project and upstream sources found the genuine upstream exterior
presheaf and the scheme-specific exterior sheaves, but no general finite-variable theorem;
searching the item's id in `lean/WeilConjectures` found no declaration. The exact searches
and unmodified result records for the added definitions are in their `mathlib_searches`.

Validation: each of the three files is compiled separately by `scompile.py`, with the two
new definitions compiled privately before their consumer. The only postponed proofs are
`SheafOfModules.siteExteriorPresheafHom_naturality` and the main theorem. Every definition
has real data; the former is a separately named proof of the naturality law explicitly
included in its owning definition node, with a complete proof docstring. No proof was
completed in stage 2, and no live source or tool was edited.

The required `deliver2.py --no-push` completed with `OK`: preflight and all three
per-file compiles passed. Its metadata check required the current new-node
`import_flags: []` field; both new records include it. All source lines are at most
100 characters, and there are no compiler warnings.

## New nodes

`def-sfb-site-exterior-sheaf` defines the sheafification of the canonical upstream exterior
presheaf on a general ringed site, its wedge-unit sections, and its map induced by a module
sheaf morphism. It records the naturality equality needed to bundle those actual sectionwise
maps. Source: 03CY and 00DM, as assembled in the item's existing proof. LeanSearch's
"Exterior power sheaf on an arbitrary ringed site is the sheafification of sectionwise
exterior powers" returned separate exterior and sheafification declarations; LeanFinder
returned sheafification Hom equivalences and ordinary exterior universality; Mathlib grep
found only the ordinary module exterior functor. DAG grep and `blueprint_refs.py search
exterior` found the existing `def-sc-sheaf-exterior-power`, which applies to schemes only.
Upstream grep found the sectionwise exterior presheaf, and that exact construction is reused.
There is no second definition of exterior algebra, exterior power, presheaf, or sheafification.
The new definition has its own module `SiteExteriorPower.lean`.

`def-sfb-site-alternating-family` defines only the subtype of sectionwise Mathlib alternating
maps satisfying every restriction identity. Source: the alternating-family side of the
item, from 00DM and the finite-variable application of 03CY. LeanSearch for "Restriction
compatible families of alternating multilinear maps between presheaves of modules" returned
ordinary multilinear restriction maps and unrelated compatible families; LeanFinder for
"A family of alternating multilinear maps between module presheaves commuting with
restriction" returned linear module morphisms and their naturality. Mathlib/project grep
found `AlternatingMap` and module-presheaf `Hom`, but no type for this family. DAG grep and
`blueprint_refs.py search alternating multilinear` found no separate definition node.
Its module `SiteAlternatingFamily.lean` uses the existing module and alternating structures.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
