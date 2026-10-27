## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePencilFiniteShrink` states
`AlgebraicGeometry.exists_relative_pencil_finite_shrink`, with its proof `sorry`.
No node statement, dependency list, proof plan or other inherited field changes.
There are no new nodes or dependency repairs. Two real-data helpers compose existing
constructions: `relativePencilSections` pulls back the ordinary global sections by
`Scheme.Modules.pullbackTopSection` and converts top-open sections back through
`homOfGlobalSection` and `SheafOfModules.unitHomEquiv`; `relativePencilHom` applies
`ProjectiveSpace.homOfGeneratingSections` to that pulled-back pair. Neither chooses an
arbitrary map or defines a second projective space, pullback or generating condition.

The node and the dependency declarations were read before writing. Source checked:
de Jong, Families of curves and alterations, §3.4, printed p.606, in the publisher PDF
https://www.numdam.org/item/10.5802/aif.1575.pdf (local PDF absent), and the node's accepted
quotient-free extraction. The local Stacks sources read were modules.tex,
lemma-s-open (01CY), constructions.tex, lemma-projective-space and the paragraph following
definition-projective-space (01NE/01NF), and more-morphisms.tex,
lemma-proper-finite-fibre-finite-in-neighbourhood (02UP). These give the precise
nonvanishing, pullback-compatible coordinate-map and finite-neighbourhood notions.
The eight-step accepted proof is reproduced in the theorem docstring with its node uses.

Every hypothesis and conclusion is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Noetherian integral domain A | `A : Type u`, `[CommRing A] [IsNoetherianRing A] [IsDomain A]` |
| Fraction field K | `K : Type u`, `[Field K] [Algebra A K] [IsFractionRing A K]` |
| U = Spec A and arbitrary s in U | All bases use `Spec (.of A)`; `s : Spec (.of A)` has no closed-point assumption |
| Proper p : Y → U | `{Y : Scheme.{u}}`, `p : Y ⟶ Spec (.of A)`, `[IsProper p]` |
| Invertible B on Y | `B : Y.Modules`, `[B.IsInvertible]` |
| Two ordinary global sections alpha, beta | `a : ULift.{u} (Fin 2) → B.sections`; the two indices encode exactly an ordered pair, and `a i` is an ordinary section, with no invariance or linearization requirement |
| Their restrictions generate B_s | `hs`, the `Epi` of `freeHomEquiv.symm` for `relativePencilSections (p.fiberι s) B a` |
| They define finite psi_s over kappa(s) | `hfiniteS` on `relativePencilHom (p.fiberι s) (p.fiberToSpecResidueField s) B a hs` |
| They generate B_K | `hK`, the same generating `Epi` after the projection `pullback.fst p (Spec.map ... (algebraMap A K))` |
| Generic coordinate map is finite | `hfiniteK` on `relativePencilHom` over the second generic-fibre projection |
| Generic coordinate map is surjective | `hsurjK : Surjective` of that same canonical coordinate map |
| Affine open neighbourhood U' of s | `∃ U : (Spec (.of A)).Opens, s ∈ U ∧ IsAffineOpen U ∧ ...` |
| Both specified base points restrict to U' | `is`, `iK`, with `his` and `hiK` identifying their composites with `U.ι` with the original residue-field and fraction-field morphisms; these factorization witnesses are unique because `U.ι` is an open immersion |
| Pair generates on Y_U' | Existential `hU`, the generating `Epi` on `pullback p U.ι` for the pulled original sections |
| Defines psi : Y_U' → P1_U' | `ψ` and its equality with `relativePencilHom (pullback.fst p U.ι) (pullback.snd p U.ι) B a hU` |
| Psi is finite and surjective | `IsFinite ψ ∧ Surjective ψ` |
| Special restriction is the specified psi_s | Equation of `baseChangeMap p (Over.homMk is his ...) ≫ ψ` with the original special coordinate map composed with `ProjectiveSpace.map ... is` |
| Generic restriction is the specified psi_K | Analogous square along `iK`, plus `ψK = relativePencilHom ... B a hK`; the square and the structure maps identify the canonical base change, not just its point map |
| A group acts on Y over U | Universally quantified arbitrary `G : Type v`, `[Group G]`, `ρ : G →* Aut (Over.mk p)`; there is no finiteness or effectiveness restriction |
| Coordinate map invariant on the generation locus | `W : Y.Opens` with pointwise membership exactly the union of the two `nonvanishingLocus` sets; its pulled pair generates by `hW`; `ρW` gives the restricted action with its inclusion compatibility; its canonical coordinate map satisfies the displayed morphism invariance for every g |
| Psi remains invariant | `∀ g, ((Over.pullback U.ι).map (ρ g).hom).left ≫ ψ = ψ`, using the actual base-changed action |
| Generic etaleness on a nonempty open is preserved | For every `V` in the original generic fibre, `Nonempty V` and `Etale (V.ι ≫` original coordinate morphism`)` imply `Etale (V.ι ≫ ψK)`; the same V is retained, and ψK is tied by equality and the base-change square to psi |

The group clause is conditional inside the conclusion, so neither a group action nor
invariance is added as a hypothesis for the main shrinking assertion. Encoding invariance
on W includes the restricted action and its compatibility with the given action; this is
what makes the phrase invariant on W meaningful when the pair itself has no linearization.
It does not assert invariance of the original sections. The witnesses W, hW and rhoW are
universally quantified, not supplied as extra assumptions of the main theorem. The target
is projective space on exactly two homogeneous coordinates, not dimension two.

Dependency declarations used (their complete signatures and docstrings were read):

- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (and its separated/universally closed parents).
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; its existing pullback instance supplies
  invertibility of every pulled module in `relativePencilHom`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, and `Scheme.fromSpecResidueField`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
  its recorded convention uses `Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `baseChangeMap`, and `Over.pullback` for the scheme and morphism base changes.
  Its main `moduleBaseChange` declaration is for a different clause, so it is not misused
  as the definition of the scheme fibre product.
- `def-weil-pbc-generating-sections`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.GeneratingSections`; the `epi` field is precisely the `Epi` condition
  used throughout, without making a duplicate predicate.
- `def-weil-pbc-morphism-to-projective-space-by-sections`:
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`,
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`, made available by Proper's public imports.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective` (surjectivity on underlying points).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.

The proof imports include the recorded upstream nonvanishing and fibre-generation
modules, `ProjectiveSpaceFunctorOfPoints`, Proper (proper permanence and
`IsProper.of_comp`), `ZariskisMainTheorem` (02UP), the public projective-space module
(projective properness), and `ProjectiveSpaceStandardCharts`. Mathlib finiteness and
local-at-target declarations are available through those imports. No consumer is edited
in this read-only checkout; the maintainer adds proof imports to external citers.

Edge cases checked: s may be the generic point or a nonclosed point; A may itself be a
field; no positive-dimensional, closed-point, flatness, reducedness, integrality of Y,
finite group, characteristic-zero or effective-action hypothesis is imposed. The empty Y
cannot satisfy generic surjectivity, as P1_K is nonempty. Empty fibres are allowed by
hfiniteS and by the finite-neighbourhood step. A zero one of the two sections is allowed
when the other generates; both zero cannot generate a nonzero invertible stalk. The group
may be trivial or infinite, and its universe is explicit and independent. The generic
etale clause explicitly retains a nonempty open, without requiring the entire fibre to
be etale. There is no constraint on the characteristic. Both K and every scheme live in
a common explicit universe u; no independent smaller test universe makes a condition vacuous.

Searches actually run (2026-10-24; wrapper output is logged in searches.jsonl):

- LeanFinder: `A pair of sections of a line bundle on a proper scheme over an integral
  base defines a finite surjective relative projective line morphism after shrinking
  around a finite special fibre`. Eight hits: finite_appTop_of_universallyClosed,
  Proj.valuativeCriterion_existence, Proj.fromOfGlobalSections and other Proj properness
  lemmas, AffineSpace surjectivity, Proj. None states this shrinking assertion.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsFinite`. Nine hits, including
  `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`, proper/finite
  equivalences and `exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`.
  These are component results, without the section-pencil, base shrinking, specified
  generic fibre and additional clauses.
- Mathlib grep through msearch: `pencil|homOfGeneratingSections|exists_isFinite_morphismRestrict`
  in AlgebraicGeometry. Two ZariskisMainTheorem hits for the finite-fibre neighbourhood
  theorem and its use; no matching theorem.
- LeanSearch: `Two global sections of an invertible module give a finite surjective
  morphism to the projective line after shrinking the base`. Eight hits; invertible-module
  projectivity and Proj-from-global-sections constructions/restriction lemmas, no match.
- `rg` over `lean/WeilConjectures` and `dag/lean_names_upstream.json` for
  `pencil|relative_pencil_finite_shrink|lem-sfb-relative-pencil-finite-shrink`: no hits.
- `rg` over `lean/Sheaf/AlgebraicGeometry`, `lean/Sheaf/Paper` and the upstream geometry
  tree for `pencil|relative.*[Pp]rojective|generationLocus|generatingLocus` found the
  component local-pencil, ample two-section-pencil, separating-pair and projective-space
  modules. Read the relevant interfaces, including the existing pair/coordinate wrappers
  and ordinary `pullbackTopSection`. No full relative-pencil shrinking theorem exists.
- Exact-name `rg` in Mathlib, `lean/WeilConjectures` and `lean/Sheaf` found none of
  `relativePencilSections`, `relativePencilHom`, `exists_relative_pencil_finite_shrink`.

Validation: scompile.py compiled the final file separately as sandbox and as its actual
library module, both clean (3.6 s each). The first compile diagnosed a missing public
import for nonvanishingLocus and unresolved Over objects at baseChangeMap; both were
repaired with the defining public import and explicit Over object type annotations.
All variables and universes are bound explicitly; autoImplicit is disabled. No diagnostic
commands, local notation, private declarations, proofs other than sorry, or hollow data
remain. No statement dispute or correction was needed.

## Second reading by NZ

The worker performed a second reading in this same session with the node and final
Lean source open. The dispatcher explicitly forbids starting another agent; this is a
self-review, with the maintainer's independent review still to follow.

The second pass matched A, K, s, properness, B and the ordered pair to the node, then
checked each Epi and each coordinate map uses the appropriate first/second projections.
In particular hfiniteS does not accidentally require special-fibre surjectivity, and
hsurjK is included separately from generic finiteness. The conclusion uses an affine open
containing s and explicitly factors both the residue-field map and fraction-field map
through it. hU refers to the original sections, not arbitrary replacement sections. The
special and generic squares are equalities of scheme morphisms, with typed Over objects;
ψK is fixed to the original generic coordinate map. The extra clauses remain implications
in the conclusion. W is exactly the generation locus, the action is over the base, and
invariance is equality of scheme morphisms after the actual pulled-back action. Finally
the original nonempty generic etale open is preserved rather than replaced by an arbitrary
open or by an assertion about total-space etaleness. No mathematical mismatch was found
and no inherited statement or proof dependency changed. Rechecked that all helpers have
real bodies and use the dependency's existing coordinate morphism.

Dry run: deliver2.py --no-push returned OK for commit cfd0a879299: preflight passes
and the module compiles. The local node comparison confirms only the lean field changed;
the module has no line above 100 characters and exactly one sorry, the named theorem.
