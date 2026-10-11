## Worker report

The item is stated by `FormalGlueing.exists_unique_bijective_h0_localization` in
`Sheaf.RingTheory.FormalGlueingH0Localization`. Its proof is `sorry`; nothing is proved.
The new module `Sheaf.RingTheory.FormalGlueingH0` defines `FormalGlueing.h0` with real
kernel/intersection data, with no postponed proof or data.

Sources read: Stacks Remark 05EL, label remark-glueing-data, especially its displayed
H^0 definition, and Proposition 05ER, label proposition-equivalence, second proof
paragraph. The local literature source is absent on this machine, so I read the
corresponding source pages https://stacks.math.columbia.edu/tag/05EL and
https://stacks.math.columbia.edu/tag/05ER. The latter gives the localization argument
through 05EQ and 05EP. The item's localization component does not require the quotient
isomorphism assumed for the whole equivalence; it holds directly by the displayed
inverse tuple in the node's proof. The flatness assumption present in this item is
retained, although localization itself does not need it.

Hypothesis and clause matching:

- Commutative rings and their map: `{R : Type uL} {S : Type vL} [CommRing R]
  [CommRing S]`, `(φ : R →+* S)`; flatness is `(hflat : φ.Flat)`, using the
  recorded `RingHom.Flat` definition, which installs `φ.toAlgebra`.
- The finite list `f_1,...,f_t`: `{t : ℕ}` and `(f : Fin t → R)`.
- The object of Glue is `(X : Data.{uL, vL, wL} φ f)`, the recorded dependency,
  not a copy. Its `M'` is the S-module, its `M i` the R_fi-module, `alpha`
  the prime/chart equivalences, `alpha_smul` their S-linearity, `alpha_overlap`
  the chart equivalences, `square` condition (a), and `cocycle` condition (b).
- The R-submodule of the product with BOTH families of compatibility equations is
  `h0 φ f X`. Its ambient product is `restrict φ X.M' × ∀ i, piece (f i) (X.M i)`.
  The first indexed intersection of kernels says
  `X.alpha i (m'/1) - (1 ⊗ m_i) = 0`; the second says
  `X.alpha_overlap i j (m_i/1) - m_j/1 = 0` for every pair i,j.
  Mathlib's tensor order is S ⊗[R] M, already used by the recorded `Data`;
  `TensorProduct.mk R S _ 1` corresponds under tensor commutativity to m_i ⊗ 1.
- Fixing a chart is `(i : Fin t)`; no positivity hypothesis on t is introduced.
- The projection p_i(h) is exactly `h.val.2 i`. This is a coordinate of the
  submodule inclusion; no separately chosen projection is used.
- Existence is `∃ π : LocalizedModule.Away (f i) (h0 φ f X) →ₗ[R]
  piece (f i) (X.M i)`. Thus the map is R-linear and has precisely the stated
  domain and codomain, without imposing extra linearity on the conclusion.
- The prescribed values are `∀ h : h0 φ f X, π (LocalizedModule.mk h 1) = h.val.2 i`.
- Exactly one means the second conjunct quantifies over EVERY R-linear π' with
  those values and concludes `π' = π`, independently of whether π' is bijective.
- The final conjunct is `Function.Bijective π`, the node's full conclusion.

Dependency declarations read and used:

- `Sheaf.RingTheory.FormalGlueingData`: `FormalGlueing.Data`, `restrict`, `piece`,
  `localize`, `extend` and the signatures/docstrings of its structural maps.
  Its defining structure and compatibility equations were read in full.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (line 27).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away` (line 142),
  the mathlib_match of def-weil-ring-localization-away (a Mathlib leaf).
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away` (line 1475),
  `LocalizedModule.mkLinearMap` (line 492), `IsLocalizedModule.lift` (line 928).
  Fractions at denominator 1 are `LocalizedModule.mk _ 1`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange` (line 661),
  and `TensorProduct.mk` for the canonical tensor inclusion. The existing Data
  module already uses the dependency's S-first base-change convention.

Edge cases checked before the final statement: t=0 gives the whole prime module as
H^0 (both intersections are top); there is no i : Fin 0, so the localization assertion
makes no demand. If f_i=0 the localized ring is zero, forcing M_i=0, and localization
of H^0 at zero is also zero. If f_i is a unit the chart itself recovers the compatible
families, as in 05EP. Zero rings and zero modules are permitted: no Nontrivial
assumption occurs. Rings may have different universes; the arbitrary module universe
wL is explicitly bound in Data. No finite-generation or presentation assumption was
introduced. There is no statement correction or disputed statement.

Searches actually run (logged in searches.jsonl):

- LeanSearch: `module of compatible sections H0 of formal glueing data for a ring map
  and finitely many localizations`: unavailable, HTTP Internal Server Error. This
  is not evidence of absence.
- LeanFinder: `Formal glueing datum compatible families module H0 localization at
  one chart is isomorphic to the chart module`: eight hits, chiefly scheme glueing
  sections and ModuleCat.Tilde sections/stalks. None defines compatible families
  for the formal-glueing datum or states this module-localization conclusion.
- Loogle: `LocalizedModule.Away, LinearMap`: four hits about finite presentation,
  free localizations and support; none is this statement or its H^0 definition.
- Mathlib grep via msearch: `FormalGlueing|glueing|BeauvilleLaszlo`: zero hits.
- `rg -n 'FormalGlueing|formal.glue|lem-weil-pbc-formal-glueing-H0-localization'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- `rg -n 'FormalGlueing|formal.glue' lean/Sheaf`: only FormalGlueingData.lean,
  which defines the datum/category, not H^0.
- `rg -l 'H.0.*glueing|glueing.*H.0' dag/nodes/sec-proper-base-change`:
  the item's node and prop-weil-pbc-formal-glueing-equivalence, neither a definition
  node for H^0. Whole DAG keyword search additionally found unrelated cohomology.
- `python3 tools/blueprint_refs.py search 'formal glueing'`: zero blueprint matches;
  ancestor lookup gives thm-weil-pbc-finite-etale-lifting.
- Name search in dag/lean_names_upstream.json for `H0|FormalGlueing|formal.glue`:
  no hits. The new declaration names are absent from source and Mathlib searches.

Validation: server compilation of both modules together succeeded with no errors
or warnings. The proof docstring follows all five steps of the node's proof:
finite kernel, exact localization, construction of the inverse tuple, compatibility
from square/cocycle, and inverse/uniqueness by localization's universal property.

## New nodes

`def-weil-pbc-formal-glueing-H0` defines the compatible-section R-submodule of a
formal glueing datum, precisely as Stacks Remark 05EL (remark-glueing-data).
It imports and uses FormalGlueing.Data; it does not redefine the datum, localization
or base change. The two intersections of kernels impose every displayed equation.
All data is built from Mathlib linear maps, kernels and lattice operations, with
no `sorry`. The module's declaration is FormalGlueing.h0. The actual LeanSearch,
LeanFinder, Loogle and grep searches above establish that there is no existing
notion to reuse; LeanSearch unavailability is explicitly recorded. The item gains
only this node in stmt_deps and otherwise changes only lean. This notion supports
the localization component of 05ER in the finite-etale-lifting algebraization route.

## Second reading by H1

I independently opened the item node, its source (Stacks Remark 05EL and the
second paragraph of Proposition 05ER), the dependency nodes, and both delivered
modules. The item-by-item correspondence is:

- The ring objects are `{R : Type uL}`, `{S : Type vL}`, each with `CommRing`,
  and the map is `(φ : R →+* S)`; `hflat : φ.Flat` is exactly the node's flat
  ring-map hypothesis. The finite list is `(t : ℕ)` and `f : Fin t → R`.
- The glueing object is `X : Data.{uL, vL, wL} φ f`. Its `M'`, `M`, `alpha`,
  `alpha_smul`, `alpha_overlap`, `square`, and `cocycle` fields are precisely
  the object and conditions of `def-weil-pbc-formal-glueing-data`; no private
  datum is introduced.
- The new definition `h0 φ f X` is the `R`-submodule of
  `restrict φ X.M' × ∀ i, piece (f i) (X.M i)`. Its first intersection of
  kernels imposes `alpha i (m'/1) = 1 ⊗ m_i`, and its second imposes
  `alpha_overlap i j (m_i/1) = m_j/1` for every ordered pair. This is exactly
  the displayed H^0 definition in 05EL, with Mathlib's `S ⊗[R] M` factor order.
- The fixed chart is `(i : Fin t)`. The asserted map has exactly the node's
  type `LocalizedModule.Away (f i) (h0 φ f X) →ₗ[R] piece (f i) (X.M i)`.
- The first conclusion conjunct is exactly the prescribed formula on every
  `LocalizedModule.mk h 1`; the second quantifies over every competing
  `R`-linear map and gives equality; the final conjunct is `Function.Bijective π`.
  Quantifier order and conjunction nesting match the node verbatim.

No mismatch was found, so no statement or module change was needed. In the
source proposition the global equivalence also assumes `R/I ≅ S/IS`; the
localization component recorded here does not need that extra assumption:
after localizing at the fixed `f i`, that element is a unit, so the unit-ideal
lemma 05EP applies. The Lean statement therefore retains exactly the item's
flatness assumption and does not silently add the global-equivalence hypothesis.

Edge cases were checked explicitly: `t = 0` makes both intersections top and
there is no chart index to instantiate; `f i = 0` and zero rings/modules are
allowed; a unit `f i` gives the chart directly; and no nontriviality,
finite-generation, characteristic, or Noetherian assumption is present.
Universes `uL`, `vL`, and `wL` are all bound and match `Data`, so no case is
excluded by a universe restriction.

Searches were rechecked with `rg` in `WeilConjectures`, `lean/Sheaf`, and the
DAG, plus Mathlib grep, LeanFinder, Loogle, and the recorded LeanSearch query.
They found `FormalGlueing.Data` but no H^0 declaration or equivalent
localization theorem. The only new notion is therefore the justified
`def-weil-pbc-formal-glueing-H0` node. Both modules compile together with
`scompile.py` without errors or warnings.
