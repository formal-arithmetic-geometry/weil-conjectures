## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeResidueIso` states
`AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_residueField_isIso`.  It binds a
scheme `S`, two `S.Modules` objects `E` and `F`, natural-number ranks `dE` and `dF`,
instances saying each module is finite locally free of its rank, a module morphism
`v : E ⟶ F`, and the conclusion `IsIso v`.

For each point `s : S`, the hypothesis installs the residue-field algebra structure
from `S.residue s : S.presheaf.stalk s ⟶ S.residueField s`.  The map
`(v.stalkLinearMap s).lTensor (S.residueField s)` is the induced map
`κ(s) ⊗_{O_{S,s}} E_s → κ(s) ⊗_{O_{S,s}} F_s`; `Function.Bijective` renders that
map as an isomorphism of modules.  The theorem proof is `sorry`, as required at
stage 2; its intended proof is the local Nakayama argument from Tag 00O0 followed
by the stalkwise isomorphism criterion.

Dependencies used: `def-pc-scheme` is Mathlib's `AlgebraicGeometry.Scheme`; the
finite locally free notion is `SheafOfModules.IsFiniteLocallyFreeOfRank` from
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.  The
stalk map is `AlgebraicGeometry.Scheme.Modules.Hom.stalkLinearMap` from
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`.

Edge cases checked: ranks `dE = 0` and `dF = 0` are admitted by the natural-number
rank binders; empty schemes are admitted because the point hypothesis is
vacuous; no equality of ranks is assumed (it follows from the fibre-isomorphism
hypothesis).

Searches made: `leanfinder` for finite locally free module maps and residue-field
criteria (only ring-level results); `loogle` for `Module.Flat Module.FinitePresentation`
residue criteria (no hits); grep of Mathlib RingTheory free-locus declarations (no
sheaf-level theorem); `rg` over WeilConjectures and the project for residue/fibre
criteria (found only the stalk criterion and the finite-locally-free class).  No
existing declaration states this theorem.

## Second reading by G1

I read the item's node, both statement-dependency nodes and their recorded
source declarations, the delivered module, and Stacks algebra.tex,
lemma-cokernel-flat (Tag 00O0), including its entire proof. The local Stacks
checkout is /home/ubuntu/c1-stacks-review; its tags/tags maps 00O0 to
algebra-lemma-cokernel-flat. The source assumes an arbitrary commutative ring
and two finite projective modules, with no Noetherian, characteristic, or
fixed common rank assumption. Its part (3) applied on local trivializations
is the scheme statement of this node. I also read modules.tex,
definition-locally-free (Tag 01C6).

Object/hypothesis/conclusion inventory and correspondence after repair:

- Scheme S [def-pc-scheme]: `{S : Scheme.{u}}`, using Mathlib's
  `AlgebraicGeometry.Scheme` (Scheme.lean:42, extending LocallyRingedSpace
  with local affine charts). Exact; no extra scheme assumptions.
- Two O_S-modules E and F: `{E F : S.Modules}`. Mathlib's
  `Scheme.Modules` (Modules/Sheaf.lean:39) is
  `SheafOfModules.{u} S.ringCatSheaf`, the sheaves of modules on the
  Zariski opens with the structure-ring sheaf. Exact category, not merely
  global-section modules or abelian sheaves.
- E finite locally free, allowing locally varying finite ranks:
  `hE : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ d : ℕ,
  (E.restrict U.ι).IsFiniteLocallyFreeOfRank d`. Exact. I opened
  the dependency's recorded `SheafOfModules.IsFiniteLocallyFreeOfRank`
  in the source LocallyFree.lean:128: it is local generators data whose
  local free index types are equivalent to Fin d. I also read
  `Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free`
  and `isFiniteLocallyFreeOfRank_of_restrict_iso_free` in source
  Modules/Sheaf.lean:561,589; these identify the predicate with the
  node's open-cover definition. Every point having such a neighbourhood
  is equivalent to an open cover on which the ranks are constant.
- F finite locally free: the analogous `hF` with F. Exact. E and F may
  have different ranks on different neighbourhoods. Intersecting their
  neighbourhoods gives the simultaneous neighbourhood used in the node,
  so independent hE and hF do not change the hypothesis.
- Morphism v of these modules: `(v : E ⟶ F)`. Exact; Scheme.Modules.Hom
  is the module-sheaf morphism, not an arbitrary function.
- Every point s and its fibre map: `h : ∀ s : S, ...`. I opened
  `Scheme.Modules.Hom.stalkLinearMap` (FlatPullbackStalk.lean:219): its
  type is the O_{S,s}-linear map from E's stalk to F's stalk induced by v.
  Mathlib's `S.residueField s` is the local ring's residue field and
  `S.residue s` is its quotient map (ResidueField.lean:45,54).
  The local Algebra instance is exactly this canonical residue action,
  not an extra hypothesis or an arbitrary action.
- Fibre map is an isomorphism: `Function.Bijective
  ((v.stalkLinearMap s).lTensor (S.residueField s))`. Exact:
  lTensor sends k tensor e to k tensor v_s(e). Tensor commutativity
  identifies this with the node's E_s tensor k -> F_s tensor k; bijectivity
  of this induced linear map is equivalent to a module isomorphism.
  The Algebra letI is only an instance supplying the specified action;
  it does not bind an auxiliary object needed in the conclusion.
- Conclusion v is an isomorphism: `IsIso v`. Exact categorical
  isomorphism of O_S-module sheaves; no weakened stalkwise-only conclusion.

Mismatch and repair (H3): the first worker's global ranks dE and dF and
instances `E.IsFiniteLocallyFreeOfRank dE` and
`F.IsFiniteLocallyFreeOfRank dF` excluded modules whose ranks vary between
components. Replaced these with hE and hF above, using the recorded
constant-rank dependency locally. No new notion, definition node, or
private copy is needed: this is an explicit hypothesis assembled from the
node's existing dependency. The item's natural-language statement is
correct and unchanged; no statement_change or citer review is required.

Edge cases: empty S makes all three point hypotheses vacuous and admits
all module morphisms, which are isomorphisms on the empty scheme. Empty
covers are allowed precisely there. Rank zero is admitted by d : ℕ,
including zero sheaves. There is no imposed equality of ranks, and ranks
need not be globally bounded: arbitrary disconnected schemes with
unbounded finite local ranks are covered. All characteristics are allowed,
with no base field hypothesis. u is explicit and arbitrary; S.Modules
uses the canonical same-universe sheaf encoding, and open neighbourhoods
are in S.Opens without an extra index-universe restriction. There are no
unbound variables or universes and no added finiteness assumptions on S.

Independent searches (logged with msearch.py):

- LeanFinder: "A morphism of vector bundles is an isomorphism if all its
  maps on fibers at points are bijective". Eight hits concerning
  topological VectorBundle/VectorPrebundle, not this algebraic-sheaf
  criterion.
- LeanSearch: "A map of finite locally free sheaves on a scheme is
  invertible when it is bijective on every residue field fiber". Service
  unavailable (Internal Server Error), recorded as unavailable.
- Loogle: `LinearMap.lTensor, Function.Bijective`. Three hits: tensor
  commutativity's bijectivity equivalence, faithful-flat tensor detection,
  and invertible-module tensor detection; none states the sheaf criterion.
- Mathlib grep: `residueField.*(bijective|isIso)|IsFiniteLocallyFree`.
  Found ring-level residue-field facts, no scheme module criterion.
- Independent rg of WeilConjectures and lean/Sheaf:
  `residue.*(iso|bijective)|finiteLocallyFree.*(iso|fiber)|isIso.*stalk`.
  Found the genuine stalkwise criterion
  `Scheme.Modules.isIso_of_bijective_stalkLinearMap` and existing local
  freeness predicates, but no residue-fibre criterion for finite locally
  free sheaves. Checked the proposed full theorem name also against
  dag/lean_names_upstream.json, WeilConjectures, and lean/Sheaf: no match.

Other repairs: added the missing copyright header and module docstring
(H8/H9). Expanded the theorem docstring to reproduce both node proof
steps: finite free stalks, cokernel Nakayama, split surjection, finite
kernel, split tensor exactness, kernel Nakayama, and stalkwise sheaf
isomorphism, naming the dependency nodes. Removed the redundant standalone
LocallyFree import (publicly imported by the used Modules.Sheaf module).
There are no definitions, hollow data, or proved statements in this
module; the sole theorem remains `by sorry` as stage 2 requires.

Validation: scompile.py compiled the repaired single module on the server
in 2.2 seconds, exit code 0, without warnings. The node lean.statement was
updated verbatim from the repaired theorem signature. No dependency
modules or new nodes are delivered.
