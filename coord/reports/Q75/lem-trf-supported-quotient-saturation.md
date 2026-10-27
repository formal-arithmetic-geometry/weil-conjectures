## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedQuotientSaturation` states
`AlgebraicGeometry.Scheme.Modules.supportedQuotientSaturation`, with one `sorry`
and no definitions. The node is unchanged except for its `lean` record. No new
notion, dependency module, or statement correction is necessary.

Hypotheses and objects, clause by clause:

- `Y : Scheme.{u}` is the arbitrary scheme; `V : Y.Opens` is its arbitrary open
  subscheme, with canonical inclusion `V.ι : V.toScheme ⟶ Y`.
- `H K : Y.Modules` are the module sheaves in Mathlib's category. The mono
  `i : K ⟶ H` represents the stated subsheaf inclusion, not an extra injectivity
  condition on an otherwise arbitrary morphism. `hK`, on every open `W` and every
  `s : Γ(H, W)`, says that membership in `Set.range (i.app W)` is equivalent to
  `H.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s = 0`.
  Thus the image subsheaf is exactly the specified supported-section subsheaf.
  This is the usual representation of a subsheaf by a monomorphism, and does not
  require a second construction of the restriction kernel. A mono of sheaves of
  modules is sectionwise injective, so `K(W)` identifies with this range.
- `[H.IsQuasicoherent] [K.IsQuasicoherent]` are precisely the two quasi-coherence
  assumptions. Neither finite type nor coherence is assumed.
- `cokernel i` is the stated `Q`; `cokernel.π i` is precisely its canonical `π`.
  They occur directly, without let binders or an arbitrary quotient map.

Conclusion, in the order of the node:

1. `(cokernel i).IsQuasicoherent` states quasi-coherence of `Q`.
2. `Epi (cokernel.π i)` states that `π` is an epimorphism of module sheaves.
3. The first universal conjunct states `π_W(s) = 0 ↔ s ∈ Set.range (i.app W)`
   for every open and every section, exactly membership in the specified `K(W)`.
4. `∀ W : Y.affineOpens, Function.Surjective ((cokernel.π i).app W.1)`
   is surjectivity on all affine opens, without asserting it on arbitrary opens.
5. `IsIso ((restrictFunctor V.ι).map (cokernel.π i))` is that the restriction
   of this same canonical projection to `V` is an isomorphism.
6. The next universal conjunct says every `t : Γ(cokernel i, W)` whose
   restriction to `W ⊓ V` is zero is itself zero, for every open `W`.
7. `Mono ((restrictAdjunction V.ι).unit.app (cokernel i))` is the equivalent
   monomorphism `Q → j_*(Q|_V)`. The arrow is Mathlib's canonical unit of open
   restriction/pushforward, not an arbitrary arrow with that source and target.

There are no quasi-compactness or separation assumptions, no affine assumption
on `Y`, and no assumption on `V` beyond openness. The single universe `u` is the
standard Mathlib universe of a scheme and its category `Y.Modules`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms
  `Scheme.Hom`, and `Scheme.Opens` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the inclusion `V.ι` has the existing canonical instance
  (def-weil-open-immersion). These are exposed through the module-sheaf import.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent abbreviation for
  `SheafOfModules`; Mathlib's `Y.Modules` is that same category specialized to
  `Y.ringCatSheaf` (def-weil-sheaf-of-modules-category).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the recorded
  `SheafOfModules.IsQuasicoherent` (pqf-def-coherent). Its
  `IsQuasiCoherentFiniteType` conjunction is intentionally not a hypothesis: the
  node assumes quasi-coherence only. The current dependency record explicitly
  lists the quasi-coherence predicate among its declarations.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.restrictFunctor`,
  `pushforward`, and `restrictAdjunction`; the latter has the signature
  `restrictFunctor f ⊣ pushforward f` for an open immersion `f`.
- The proof-only import is the recorded
  `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, whose
  `Scheme.Modules.quasiCoherent_cokernel_image` gives quasi-coherence of the
  cokernel, its epimorphic projection, the local-image description of its kernel,
  and affine surjectivity. Its complete signature and proof docstring were read.

Source checks: read `literature/stacks-project/properties.tex` at
`lemma-sections-supported-on-closed-subset` (Tag 07ZP), especially the sectionwise
restriction-kernel sequence in the proof of (3), and `divisors.tex` at
`definition-strict-transform` (Tag 080D (1)). Retrocompactness in 07ZP is used to
prove quasi-coherence of the supported subsheaf; the item assumes that
quasi-coherence instead, so it does not inherit retrocompactness. Residual-support
vanishing is the node's explicit affine-lifting argument, included in the theorem
docstring together with its other three proof steps.

Edge cases checked mathematically before writing:

- `V = ⊥`: `K = H` as a subsheaf and `Q = 0`; restriction is the isomorphism
  between zero sheaves on the empty scheme and the unit from zero is mono.
- `V = ⊤`: `K = 0`, so the quotient map is an isomorphism and saturation is
  ordinary injectivity of restriction to the same open.
- `Y` empty, `H = 0`, or `W = ⊥`: the statement remains valid; none is excluded.
- On `Spec ℤ`, with `V = D(2)` and `H = O ⊕ (ℤ/2)~`, the supported subsheaf
  is the torsion summand and the quotient is `O`; restriction has zero kernel.
- In the proof the overlaps of affine lifts need not be affine: injectivity on
  every open contained in `V` provides their compatibility. Likewise the final
  saturation assertion covers nonaffine `W` by affine opens.

Searches for an exact existing statement:

- `msearch.py ... leanfinder` with query “Quotient of a quasi coherent sheaf by the
  kernel of restriction to an open subset is quasi coherent, unchanged on that
  open, and has injective restriction to it”: eight hits concerning
  `SheafOfModules.QuasicoherentData` and `IsQuasicoherent`; none states this lemma.
- `msearch.py ... loogle '"SheafOfModules", "cokernel"'`: twelve hits on free
  presentations and cokernel coforks; none is this supported quotient theorem.
- `msearch.py ... leansearch` with query “Quotient of a quasi coherent module
  sheaf by all sections vanishing on an open has injective restriction to that
  open”: eight hits, including `SheafOfModules.IsQuasicoherent.mk`,
  `Scheme.Modules.restrict_obj` and `SheafOfModules.isQuasicoherent`; no match.
- `msearch.py ... grep 'supported|saturat|cokernel' AlgebraicGeometry/Modules`:
  five hits in `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`, concerning tilde
  presentations and cokernels, not supported-section quotient saturation.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed name and `restrictionKernel`
  found no duplicate. A broader `supported|Supported|saturat|Saturat` search in
  the module and paper source directories found support/cohomology material,
  not the theorem. Searching the item id in both Lean roots found no declaration.

Validation: `scompile.py Q75 lem-trf-supported-quotient-saturation` successfully
compiled the file in both sandbox and library module modes, with no errors or
warnings (4.8 s and 3.3 s respectively). The maximum source line width is 89.
The required delivery dry run and final delivery are run after this report.

## Second reading by Q75

This is the author's second reading; the maintainer performs the independent
review under the direct-delivery brief. Reopened the node and the complete Lean
file and checked all seven conclusion clauses in the order listed above.
`[Mono i]` and `hK` jointly represent the specified subsheaf, without strengthening
it; `Set.range` is membership in that actual subsheaf, rather than the kernel of
an arbitrary map. The quotient and both canonical arrows use existing Mathlib
constructions. In particular the final map is the restriction adjunction's unit
and the isomorphism clause applies to the restriction of the canonical quotient
map itself. The predicate used is quasi-coherence, not the dependency module's
stronger finite-type conjunction. Both residual vanishing and its equivalent
mono formulation are present. No clause was lost, no compactness assumption was
introduced, all variables and the universe are explicitly bound, and only the
requested theorem proof is postponed. No mismatch or statement fault was found;
no correction, new node, or dependency repair was made.
