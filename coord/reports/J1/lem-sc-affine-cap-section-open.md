## Worker report

The module `Sheaf.AlgebraicGeometry.AffineCapSectionOpen` states
`AlgebraicGeometry.Scheme.Modules.affine_cap_section_open`, with a single `sorry` proof.
It states both clauses of the node. No definition, dependency module, or node correction is needed.

Hypotheses and conclusions, clause by clause:

- An arbitrary scheme Y: `(X : Scheme.{u})`, with explicitly declared universe `u`.
- An invertible O_Y-module M: `(M : X.Modules) [M.IsInvertible]`.
- A global section s: `(s : M.val.presheaf.obj (Opposite.op ⊤))`, the module of sections
  over the whole scheme, without choosing a trivialization.
- An affine open U: `(U : X.Opens) (hU : IsAffineOpen U)`.
- The intersection U cap Y_s is affine: the first conjunct is
  `∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X, x ∈ V ↔ x ∈ U ∧ ...`.
  The omitted predicate is written in full in the signature: the germ of s is outside
  `(IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule ... stalk ...)`.
  This is precisely the nonvanishing predicate of the recorded ample-module dependency.
  Equality of underlying sets is expressed by pointwise membership equivalence, so V is
  exactly the intersection, not an affine subopen or an affine neighbourhood. Its open
  structure is uniquely determined by this set. No additional openness hypothesis is added.
- The same holds for every section of every positive tensor power: the second conjunct
  quantifies `∀ n : ℕ, 0 < n → ∀ t : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤)`.
  It repeats the same affine-open conclusion with the stalk and germ of `M.tensorPow n`.
  There is no new invertibility assumption on the tensor power.

Dependency declarations read and used:

- `def-pc-scheme` is a Mathlib leaf; its `mathlib_match` is
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`. The module uses `Scheme` and `Scheme.Opens`;
  no scheme morphism is required by this statement.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`. Its full class signature and
  `exists_isoUnit` field were read: local triviality over open neighbourhoods.
  The same module's `tensorPow` is the recursive tensor product with the structure
  sheaf in degree zero; its docstring and signature were read.
- `def-weil-pbc-ample-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsAmple`
  in `Sheaf.AlgebraicGeometry.Ample`, imported by this module. Its complete definition
  was read; the current statement uses its existing imported tensor-power, germ, stalk,
  and ideal-times-module APIs and its exact nonvanishing predicate. Ampleness itself is
  not a hypothesis. There is no separate named nonvanishing-open definition in that file,
  so the theorem expresses the set by that predicate without introducing another definition.
- `AlgebraicGeometry.IsAffineOpen` in `Mathlib.AlgebraicGeometry.AffineScheme` means
  that the open subscheme is affine. `TopCat.Presheaf.germ` and `stalk`, together with
  `IsLocalRing.maximalIdeal` and Mathlib's ideal action on submodules, are the same APIs
  used by the recorded dependency.

Edge cases checked before writing: empty X and empty U give the empty affine scheme;
zero sections have empty nonvanishing locus; for a trivial line bundle and a function f,
the locus on Spec R is D(f), including f=0 and units. Positive powers include n=1 and
all larger natural numbers; n=0 is deliberately outside the second clause, as the node
says positive. There is no field, characteristic, Noetherian, separatedness, nonemptiness,
or quasi-compactness restriction on X. An arbitrary universe u is allowed.

Source checked: https://stacks.math.columbia.edu/tag/01PV (Properties Lemma 28.27.4).
The local `literature/stacks-project/properties.tex` is absent on this machine, so the
source tag was opened directly. The lemma has exactly the hypotheses used here; its
algebra proof uses Sym_R(N)/(s-1). The positive-power clause follows by applying it to
an invertible tensor power. The theorem docstring carries all three DAG proof steps,
including their dependency ids. No statement dispute or fault was found.

Searches performed (2026-10-11):

- msearch leanfinder: "The intersection of an affine open with the nonvanishing locus
  of a global section of an invertible sheaf is affine". Eight hits; the closest is
  `AlgebraicGeometry.IsAffineOpen.basicOpen`, which concerns a section of the structure
  sheaf and does not cover an arbitrary invertible module.
- msearch loogle: `AlgebraicGeometry.IsAffineOpen`. Twelve hits, including basicOpen
  and affine-open image/preimage results; no exact line-bundle statement.
- msearch leansearch: "affine open intersect nonvanishing locus invertible module section".
  Service unavailable (Internal Server Error); no result returned.
- msearch grep in Mathlib/AlgebraicGeometry:
  `nonvanishing|nonVanishing|affine.*section|section.*affine`. Twenty-five displayed hits
  concern basic opens, structure-sheaf sections, and unrelated affine criteria; no exact match.
- rg in WeilConjectures and lean/Sheaf for nonvanishing, affine sections, and
  `affine_cap_section_open`; rg for the blueprint id in WeilConjectures; rg in
  `dag/lean_names_upstream.json` for the intended declaration name. No exact statement or
  name collision. The existing `AffineCapSectionOpenAlgebra` is the algebraic proof input,
  not this scheme statement. Upstream `Modules.ZeroLocus` and `Modules.AmpleFamily` use
  zero-locus complements for morphisms of invertible modules, but do not state this theorem.
  `ProjectiveSpace.CoordinateCover` defines nonvanishing for its different section datum;
  it does not duplicate the germ-based predicate from the recorded dependency.

Validation: scompile completed with exit code 0 in 1.8 seconds, with no errors or warnings.
`deliver2.py J1 lem-sc-affine-cap-section-open --no-push` printed OK: the module compiles
and preflight passes except for the independent second reading, which the second worker
writes. Nothing was pushed. The independent reading is deliberately left for that worker.

## Second reading by J1

Independent reading of the node, its three statement dependencies and their declarations,
the sandbox module, and Stacks `properties.tex`, section `section-ample` and
`lemma-affine-cap-s-open` (Tag 01PV). The local Stacks checkout is absent; I fetched and
read the upstream TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex.
The section introduces the nonvanishing locus by the maximal-ideal-times-stalk predicate;
it imposes no standing finiteness, separation, field, or characteristic hypotheses.
The positive-power clause is the node's direct application of 01PV to an invertible
power, rather than a separate clause printed in 01PV.

Objects, hypotheses, and conclusions checked individually:

- Scheme Y: `(X : Scheme.{u})`, with `universe u` explicitly declared. Verdict: exact,
  using the `def-pc-scheme` Mathlib leaf, with no extra scheme hypotheses.
- Invertible module M: `(M : X.Modules) [M.IsInvertible]`. I opened Mathlib's `Modules`
  definition and the recorded upstream `IsInvertible` class and `exists_isoUnit` field.
  These are sheaves of modules over the structure sheaf, locally trivial of rank one;
  local triviality also entails the quasi-coherence in the dependency node's wording.
  Verdict: exact, no added trivialization or freeness of global sections.
- Global section s: `(s : M.val.presheaf.obj (Opposite.op ⊤))`. Verdict: all global
  sections of this very module, not functions or morphisms for a different bundle.
- Affine open U: `(U : X.Opens) (hU : IsAffineOpen U)`. I opened `IsAffineOpen`, whose
  body is `IsAffine U` for the open subscheme. Verdict: exact.
- Nonvanishing locus Y_s: the germ at x is outside
  `(IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule ... stalk ...)`.
  I opened `Sheaf.AlgebraicGeometry.Ample` and its dependency node; this is precisely
  their predicate, expressing nonzero residue-field value, not merely a nonzero germ.
  Verdict: exact. No new or private definition is introduced.
- First conclusion: `∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X, x ∈ V ↔ ...` specifies
  precisely `x ∈ U ∧ x ∈ Y_s`. Extensionality determines V uniquely as the intersection;
  existence adds no stronger condition since the source already calls this locus open.
  Verdict: exact affineness of the whole intersection, not just a covering by affines.
- Positive powers and arbitrary sections: `∀ n : ℕ, 0 < n → ∀ t :
  (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ...`. I read upstream `tensorPow`:
  degree zero is the tensor unit, successor is tensor product over the structure sheaf.
  The repeated existential open and membership equivalence specify exactly U intersect
  the nonvanishing locus of t. Verdict: exact for every positive power and every section,
  with no extra instance assumption on powers. The fixed U is arbitrary throughout.

Edge cases: empty schemes and empty affine opens are allowed; the resulting locus is
empty and affine (Spec of the zero ring). The zero section has empty nonvanishing locus.
A globally trivial invertible module on Spec R gives the usual D(f), including f=0 and
units. There is no index family, nonemptiness, characteristic, Noetherian, separatedness,
or quasi-compactness assumption. The second clause excludes exactly n=0, as requested,
and includes n=1. The universe u is arbitrary; `X.Modules` uses the standard Mathlib
scheme-module universe convention, and invertible modules are locally rank one, so this
excludes no line-bundle case up to the usual universe enlargement. All variables and
universes are explicitly bound.

Independent searches (2026-10-11):

- LeanFinder via msearch: "affine open complement vanishing section locally free rank one
  sheaf" returned eight results, including `IsAffineOpen.basicOpen`, localization and
  denominator lemmas. None states the invertible-module intersection theorem.
- Loogle via msearch: unqualified `IsAffineOpen` was unrecognized; the corrected query
  `AlgebraicGeometry.IsAffineOpen` returned twelve declarations, whose signatures I read.
  The closest, `IsAffineOpen.basicOpen`, is for structure-sheaf sections only.
- LeanSearch via msearch: "affine intersection complement zero scheme line bundle
  section" was unavailable (Internal Server Error); no mathematical verdict inferred.
- Independent rg across Mathlib AlgebraicGeometry, upstream WeilConjectures, and
  project lean/Sheaf for affine with zeroLocus, vanish, section, complement, and the
  intended declaration name. I also inspected `Modules.ZeroLocus` and `Modules.AmpleFamily`
  for affine declarations, and checked `dag/lean_names_upstream.json` for the new name.
  No exact statement or name collision found. The algebra-only companion is distinct;
  existing zero-locus APIs concern module morphisms and do not state this theorem.

No new nodes, dependency modules, or statement correction occur in this delivery.
No mismatch was found, and the correct Lean and node were left unchanged. The single
named theorem has only `sorry` as its proof, no definitions or hidden data holes. Its
module and theorem docstrings name 01PV and the blueprint id; the theorem docstring
carries all three node proof steps with their dependencies. The sole import supplies
the recorded nonvanishing/tensor/stalk APIs. The namespace, name, header, and 100-character
line width conform. I mechanically checked that `lean.statement` is verbatim equal to
the theorem signature. Independent scompile succeeded (exit 0, 1.8 s, no warnings).
