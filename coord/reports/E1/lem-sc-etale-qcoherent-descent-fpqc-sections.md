## Worker report

Module `Sheaf.AlgebraicGeometry.FpqcTensorSections` states
`AlgebraicGeometry.Scheme.Modules.existsUnique_tensorSections_of_fpqcCover`.
Its only proof is `sorry`; no definitions or auxiliary results are introduced.
The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence:

- S and T are schemes: `{S T : Scheme.{u}}`; the arbitrary morphism T → S is
  `(f : T ⟶ S)`. No étaleness, separation, finiteness or base-field condition is imposed.
- F is an O_S-module: `(F : S.Modules)`; quasi-coherence is `[F.IsQuasicoherent]`.
- The covering family is `{I : Type v} (Ti : I → Scheme.{u}) (g : ∀ i, Ti i ⟶ T)`;
  its fpqc property is `hg : Presieve.ofArrows Ti g ∈ Scheme.fpqcPrecoverage T`.
  This is the dependency's recorded flat, jointly surjective, quasi-compact-cover condition.
- f_i = f ∘ g_i is `g i ≫ f`, with sections
  `s : ∀ i, Γ((tensorPullback (g i ≫ f)).obj F, ⊤)`.
- The pairwise fibre product is `pullback (g i) (g j)`; the projection maps are
  `pullback.fst (g i) (g j)` and `pullback.snd (g i) (g j)`.
- `hs` expresses equality of the two pulled-back sections for every i and j.
  Each is pulled back by `tensorSectionsUnit` along its projection and then identified
  with the pullback from S by `tensorSectionsComp`. The left section lies in the
  pullback along `fst ≫ g i ≫ f` and the right along `snd ≫ g j ≫ f`.
  `pullback.condition_assoc (f := g i) (g := g j) f` equates those arrows.
  Its symmetric equality, mapped through `fun k ↦ (tensorPullback k).obj F`,
  gives an `eqToHom` from the right module to the left. Its component on ⊤ transports
  the right section to precisely the left section's module, with no extra condition.
- The conclusion is `∃! t : Γ((tensorPullback f).obj F, ⊤), ∀ i, ... = s i`.
  The displayed restriction is `tensorSectionsUnit (g i)` followed by
  `(tensorSectionsComp (g i) f).hom.app F` on ⊤. Thus t restricts to each s_i,
  and uniqueness concerns exactly this simultaneous restriction property.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `pqf-def-coherent` records `Sheaf.AlgebraicGeometry.Coherent`. Its full module docstring
  explicitly uses Mathlib's `SheafOfModules.IsQuasicoherent` for the quasi-coherent clause;
  `RingedSpace.IsCoherent` is only the coherent clause and is not appropriate here.
  We therefore import `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` and use
  that very same `IsQuasicoherent`, without duplicating any definition or imposing coherence.
- `Sheaf.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, imported transitively by the
  section-map dependency. It is the recorded tensor formula, not Mathlib abstract pullback.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and
  `pullback.condition_assoc`, transitively imported through the site modules.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`.
- `Sheaf.AlgebraicGeometry.EtaleTensorSections`:
  `AlgebraicGeometry.Scheme.Modules.tensorSectionsUnit` and `tensorSectionsComp`.
  Their complete signatures quantify over arbitrary scheme morphisms, even though the
  later presheaf in that module specializes them to the small étale site. They provide
  exactly the unit-normalized section pullbacks requested by this node.

Source checked: https://stacks.math.columbia.edu/tag/03DT, Lemma 35.8.1 and its proof
via Tag 023T. The local literature source is not present on this machine, so the
published Stacks page was opened directly. The declaration docstring contains all three
node proof steps and their descent and pullback inputs.

Edge cases checked before writing:

- A singleton identity cover gives the original section, using the identity section law.
- An empty index type is allowed. An empty fpqc cover forces T to be empty, and its
  module has exactly one global section, so the unconditional uniqueness is correct.
- Empty individual Ti and empty fibre products introduce only unique zero sections.
- F = 0 has only the zero section, so both compatibility and unique gluing hold.
- No quasi-compactness of T or of each individual g_i is assumed; the family condition
  is the genuine fpqc one recorded by the dependency.
- Universes u and v are bound explicitly; v is independent because the family index
  can be arbitrarily large. All schemes live in u; no characteristic is restricted.

Searches for an existing statement:

- `msearch.py leansearch`, query "compatible global sections of a quasi coherent pullback
  descend uniquely along an fpqc covering family": service unavailable (Internal Server
  Error), logged; no mathematical verdict assigned to this unavailable service.
- `msearch.py leanfinder`, same query: eight hits, including generic presheaf
  `CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows`, but none stating
  this tensor-pullback fpqc result.
- `msearch.py loogle`, query `AlgebraicGeometry.Scheme.fpqcPrecoverage`: eight hits
  identifying the cover predicate and related cover lemmas, no section descent result.
- `msearch.py grep`, regex `fpqc.*section|sections.*fpqc`: no Mathlib hits.
- `rg` in source `WeilConjectures/` and project `lean/Sheaf/`, regex
  `fpqc.*[Ss]ection|exists_sections|sections_ext|lem-sc-etale-qcoherent-descent-fpqc-sections`:
  found upstream `Modules/FpqcSections.lean` and its usages. The full signatures and
  docstrings of `sections_ext_of_mem_fpqcTopology` and
  `exists_sections_of_mem_fpqcTopology` were read: they are sieve-form results using
  abstract pullback, separate uniqueness and existence, and all further-pullback
  compatibility. They do not exactly state this family result, as the node's existing
  lead note also records.
- Exact-name searches in Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` found no existing
  `existsUnique_tensorSections_of_fpqcCover` or `FpqcTensorSections` declaration.

Validation: local compile initially lacked the recently landed dependency's .olean;
server compilation was used as instructed and passed cleanly in 2.6 seconds. The first
dry run encountered an unrelated concurrently modified node in the shared delivery clone;
rerunning the delivery tool printed OK: server compilation and preflight passed, apart
from the second-reading section that the independent reader must supply. Nothing pushed. No statement faults, disputes, new nodes or dependency
replacement modules were needed.

## Second reading by E1

I independently read the node, its source (Stacks Tag 03DT, Lemma 35.8.1, with
the fpqc argument invoking Tag 023T), and
`Sheaf.AlgebraicGeometry.FpqcTensorSections.lean`.

The statement items match as follows. The schemes and morphism are rendered by
`{S T : Scheme.{u}}` and `f : T ⟶ S`, with no extra separation, finiteness,
Noetherian, or base-field assumption. The coefficient module and quasi-coherence
hypothesis are `F : S.Modules` and `[F.IsQuasicoherent]`. The covering family is
`I : Type v`, `Ti : I → Scheme.{u}`, `g : ∀ i, Ti i ⟶ T`, with
`hg : Presieve.ofArrows Ti g ∈ Scheme.fpqcPrecoverage T`. Local sections are
`s : ∀ i, Γ((tensorPullback (g i ≫ f)).obj F, ⊤)`, i.e. sections of
`f_i^* F` after writing `f_i = g_i ≫ f`. The compatibility clause `hs` compares
the two pullbacks along the fibre-product projections using `tensorSectionsUnit`,
`tensorSectionsComp`, and `eqToHom` along `pullback.condition_assoc`; its
direction transports the right section into the left module. The conclusion is
exactly the unique `t : Γ((tensorPullback f).obj F, ⊤)` whose canonical
restriction along every `g i` equals `s i`.

No mismatch was found and no Lean or node change was required. The tensor
pullback maps are the declarations from `EtaleTensorSections`, and the fpqc
predicate is the recorded Mathlib `fpqcPrecoverage`; no private notions are used.

Edge cases checked: singleton identity covers, empty index families (which can
cover only the empty scheme), empty members and fibre products, and the zero
module. Universes `u` and independent family index universe `v` are explicit;
there is no characteristic restriction or `n` parameter.

I repeated exact-name and conceptual searches in Mathlib, `WeilConjectures`, and
`lean/Sheaf`, including LeanFinder/Loogle/grep searches for fpqc section descent.
The nearby `FpqcSections` declaration is sieve-form with separate existence and
uniqueness and all-further-pullback data, so it does not state this family-form
theorem. No existing declaration or dependency module states this theorem exactly.
