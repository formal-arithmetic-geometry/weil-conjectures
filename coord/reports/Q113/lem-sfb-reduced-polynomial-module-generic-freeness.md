## Worker report

Stage 2, group Q113, item lem-sfb-reduced-polynomial-module-generic-freeness.
The inherited BLOCKED ending was from stage 1: Q110's accepted delivery split the
proof but supplied no Lean statement. The live node has no Lean record and no
released repair note. This packet preserves its accepted statement and nine-step
proof verbatim and supplies its stage-2 statement.

The theorem is `MvPolynomial.isOpen_dense_polynomialModuleGoodLocus` in
`Sheaf.RingTheory.ReducedPolynomialModuleGenericFreeness`. Its sole postponed
proof is `by sorry`; its docstring contains the complete nine-step accepted
natural-language proof and all five proof-dependency node names.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`. Reducedness:
  `[IsReduced R]`, Mathlib's assertion that every nilpotent element is zero,
  equivalent over rings to the stated positive-power condition, including R=0.
- n nonnegative: `(n : ℕ)`; the variable set is `Fin n`, so zero variables are
  included. P is `MvPolynomial (Fin n) R` with Mathlib's constants `C`.
- M is an arbitrary P-module: `(M : Type v) [AddCommGroup M]` and
  `[Module (MvPolynomial (Fin n) R) M]`. The ring and module universes u and v
  are independent and explicitly bound; all other variables are bound too.
- Finite generation over P: `[Module.Finite (MvPolynomial (Fin n) R) M]`.
  This imposes neither finite presentation nor finiteness over R.
- R_f is `Localization.Away f`. The localized module is the standard
  `LocalizedModule ((Submonoid.powers f).map MvPolynomial.C) M`, with original
  scalar ring P. This is the same fraction construction as localization of
  the underlying R-module: the denominators C(f^a) are in bijection with
  f^a because C is injective. The assignment m/C(f)^a to m/f^a and its inverse
  have exactly the same equivalence relation: for some k,
  C(f)^k • (C(f)^b • m - C(f)^a • m') = 0 becomes
  f^k • (f^b • m - f^a • m') = 0 on restriction along C. The zero ring and f=0
  do not require cancellation and satisfy this identification too.
- The module action over `MvPolynomial (Fin n) (Localization.Away f)` is
  `MvPolynomial.localizedPolynomialModule`, constructed from
  `MvPolynomial.isLocalization` and `LocalizedModule.moduleOfIsLocalization`.
  This is canonical localization of the scalar action: p/C(f)^a acting on
  m/C(f)^b is (p • m)/C(f)^(a+b). In particular X_i(m/f^a)=(X_i m)/f^a,
  precisely the action in the node. The base action
  `localizedPolynomialBaseModule` restricts this action along constant
  polynomials via `Module.compHom`; no arbitrary module action is supplied.
- Freeness over R_f: `@Module.Free ... (localizedPolynomialBaseModule ...)`.
  Mathlib Free permits every basis index set, including infinite and empty.
- Finite presentation over the localized polynomial ring:
  `@Module.FinitePresentation ... (localizedPolynomialModule ...)`.
- G is `MvPolynomial.polynomialModuleGoodLocus R n M`. Its defining predicate
  is `∃ f : R, f ∉ p.asIdeal ∧ Free ... ∧ FinitePresentation ...`, exactly
  the union of the principal opens D(f) selected by both properties. The
  underlying space of `AlgebraicGeometry.Spec (CommRingCat.of R)` is
  `PrimeSpectrum R` with the same topology, so no scheme-theoretic datum is
  being replaced by a different notion.
- Open and dense are respectively `IsOpen G` and `Dense G`, joined by `∧`.
  No rank bound or global single f is asserted, and no domain, Noetherian,
  nonzero-ring or original finite-presentation assumption is present.

Dependency declarations read and used, with modules:

- def-weil-pbc-mv-polynomial-ring: `MvPolynomial`, `MvPolynomial.algHom_ext`
  (`Mathlib.Algebra.MvPolynomial.Basic`), and `MvPolynomial.aeval`
  (`Mathlib.Algebra.MvPolynomial.Eval`). The statement uses the actual
  polynomial ring, constants and its standard scalar-localization algebra.
- def-weil-finitely-generated-module: `Module.Finite`
  (`Mathlib.RingTheory.Finiteness.Defs`), meaning FG of the top submodule.
- def-weil-ring-localization-away: `Localization.Away`
  (`Mathlib.GroupTheory.MonoidLocalization.Away`), with its ring structure
  supplied through `Mathlib.RingTheory.MvPolynomial.Localization`.
- def-weil-pbc-module-localization-away: `LocalizedModule`,
  `LocalizedModule.Away`, `LocalizedModule.mkLinearMap`, `IsLocalizedModule.lift`
  (`Mathlib.Algebra.Module.LocalizedModule.Basic`). The declaration record
  explicitly includes the general LocalizedModule construction; here its
  denominators are the powers of C(f). `moduleOfIsLocalization` from the same
  module gives the canonical extended scalar action with real data.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`, `Spec.map`
  (`Mathlib.AlgebraicGeometry.Scheme`); its underlying topological space is
  PrimeSpectrum, whose `basicOpen` is exactly f not in the prime ideal.
- def-weil-pbc-free-module: `Module.Free`
  (`Mathlib.LinearAlgebra.FreeModule.Basic`), with unrestricted basis index.
- def-sc-finitely-presented-module: `Module.FinitePresentation`
  (`Mathlib.Algebra.Module.FinitePresentation`), finitely many generators and
  finitely generated relations, equivalent to the stated finite free presentation.
- New definition dependency: `MvPolynomial.polynomialModuleGoodLocus`,
  `localizedPolynomialModule`, `localizedPolynomialBaseModule`
  (`Sheaf.RingTheory.PolynomialModuleGoodLocus`).

Stated proof dependencies are imported without `public`:
`Sheaf.TraceFormula.PolynomialShearLeadingCoefficient`
(`Algebra.exists_polynomial_shear_leading_coefficient`) and
`Sheaf.RingTheory.FinitelyPresentedOverSubring`
(`Module.FinitePresentation.of_finiteType_subring`). Their full signatures
and source docstrings were read. The former covers m+1 variables and the
empty exponent list; the latter uses a ring map, its finite-type predicate,
and finite presentation for the restricted module. The radical Mathlib match
is supplied by `Mathlib.RingTheory.Spectrum.Prime.Topology`
(`PrimeSpectrum.zeroLocus_eq_iff`) and `Mathlib.RingTheory.Ideal.Operations`
(`Ideal.radical_eq_sInf`). The two newly split proof prerequisites
lem-sfb-polynomial-good-locus-localization and
lem-sfb-polynomial-good-locus-extension have no Lean record or Mathlib match
in the read base; no import is invented for them. They are proof-only
prerequisites and do not prevent stating this theorem. Their later statements
can use the shared good-locus definition introduced here.

Source checked: the full polynomial-algebra proof of Tag 051Z in
`literature/stacks-project/algebra.tex`, including equation-good-locus,
051W/051X and the two inductions. The current blueprint unit is
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
part (3), through the inherited supporting chain recorded on the item.
The source's cyclic-filtration typo R/J_i is already corrected to P/J_i
in the accepted split; no node statement correction is needed here.

Edge cases checked mathematically before writing:

- R=0: Spec R is empty and every subset is dense there; all fractions exist.
- f=0: both localized scalar ring and module are zero; D(0) is empty, so it
  contributes no point. f=1 gives the original module with its original action.
- M=0: the empty basis is allowed and the zero module is finitely presented;
  f=1 shows G=Spec R.
- n=0, R=Z, M=Z/2: D(2) lies in G because M_2=0 and is dense in Spec Z.
  There is no erroneous assertion of freeness before localization.
- R=k×k and n=0, with unequal module ranks on the factors: the two idempotent
  principal opens cover Spec R and allow different ranks; a single global
  basis is not required.
- n>0, M=P: the base basis consists of all monomials and can be infinite;
  finite presentation is over P_f, where the rank is one. Finite base rank
  is deliberately absent.
- Reduced non-Noetherian rings (for example a polynomial ring in infinitely
  many variables) are permitted; no Noetherian instance is bound.
- Reducedness is meaningful: for R=k[eps]/(eps^2) and M=k with n=0, the only
  nonempty principal chart does not make M free over R; the claim would fail
  without the reducedness hypothesis.

Searches before introducing declarations:

1. msearch.py leanfinder, query "A finite module over a polynomial ring over a
   reduced ring is free over the base and finitely presented over the polynomial
   ring on a dense union of principal opens": eight hits, including
   Module.FinitePresentation.exists_free_localizedModule_powers and standard
   smooth-presentation results, no exact statement.
2. msearch.py loogle, query "LocalizedModule, MvPolynomial,
   Module.FinitePresentation": zero hits. Query "MvPolynomial, Module.Free,
   Module.FinitePresentation": zero hits.
3. msearch.py grep, query "generic.*free|generic.*flat|LocalizedModule.*MvPolynomial"
   restricted to RingTheory: only a genericPolyMap comment in FreeCommRing.
   Query "goodLocus|good_locus|polynomialModuleGoodLocus": zero hits.
4. msearch.py leansearch, query "The union of principal opens where a localized
   polynomial module is free over the localized base and finitely presented over
   the polynomial ring": eight hits, headed by existing localization/free-locus
   results. Module.freeLocus means pointwise freeness over the local ring, with
   no polynomial finite-presentation condition. isOpen_freeLocus assumes finite
   presentation over the base; it is not this definition or theorem.
5. rg of lean/WeilConjectures and lean/Sheaf for generic freeness/flatness and
   localized polynomial actions found the domain/Noetherian generic-freeness
   statements, no reduced-base version. The source signatures of
   noetherian_algebra_module_generic_freeness and
   finitely_presented_algebra_module_generic_freeness require a domain and
   respectively Noetherianity or original finite presentation, so neither
   matches. The upstream FreeLocus module likewise gives domain generic freeness.
   rg for the item id in lean/WeilConjectures found no attachment.
6. rg of lean/Sheaf, lean/WeilConjectures and dag/lean_names_upstream.json for
   all four new declaration names found no matches.
7. rg in dag/nodes for good locus, together with
   tools/blueprint_refs.py search "polynomial good locus" (zero blueprint
   matches), found the item and the two good-locus lemmas, but no definition
   node. The latter two have no Lean record. The ancestor command returns
   blueprint.from.node=None; the new definition preserves that inherited
   null ancestor and prepends the item to the full via chain.

Validation: both delivered modules compile separately and in dependency order
with scompile.py against the live server build. The helper module has no
postponed proof or data; the theorem has precisely one sorry. No errors or
warnings were reported. All source lines are at most 100 characters.

No statement fault or STATEMENT-DISPUTED flag remains. The original node is
changed only in lean and by adding the new definition to stmt_deps.

## New nodes

`def-sfb-polynomial-module-good-locus` defines the canonical localized polynomial
and base actions and the exact union G used in the item, following equation-good-locus
and the polynomial case of Tag 051Z. Its module is
`Sheaf.RingTheory.PolynomialModuleGoodLocus`, with one definition and two
canonical-action abbreviations listed in lean.declarations. It uses Mathlib's
actual fraction-module construction and localization instance; there is no
postponed existence choice. The searches above and in its mathlib_searches
found no definition node or declaration for the combined locus, although all
its ingredients already exist and are imported. The new definition needs no
reducedness or finite-generation assumptions and is reusable by both
proof-only good-locus lemmas. No dependency modules or statement correction
are included.

Preflight metadata repair: the live gate requires `import_flags: []` on the new
node and records the definition signature starting at `def`, omitting the
`noncomputable` modifier. The packet now follows those current requirements.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
