## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSmoothPrimeSchemeNeighbourhood` states
`AlgebraicGeometry.exists_principal_open_smooth_of_isSmoothAtPrime`, with `sorry`
as its entire proof. No definitions, extra nodes, dependency repairs, or statement
corrections are needed. The existing node is changed only in `lean`.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A morphism of schemes f:X→S | `{X S : Scheme.{u}} (f : X ⟶ S)` |
| Arbitrary commutative chart rings R and A | `{R A : Type u} [CommRing R] [CommRing A]` |
| W=Spec A is an affine open subscheme of X | `iW : Spec (CommRingCat.of A) ⟶ X` with `[IsOpenImmersion iW]` |
| V=Spec R is an affine open subscheme of S | `iV : Spec (CommRingCat.of R) ⟶ S` with `[IsOpenImmersion iV]` |
| f(W) lies in V, and φ is the induced ring map | `[Algebra R A]` and `hchart : iW ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iV` |
| x corresponds to a prime q in W | `(q : PrimeSpectrum A)`; the point x is `iW q` |
| φ is smooth at q, in the principal-localization sense | `(hsmooth : Algebra.IsSmoothAtPrime R q)` |
| There exists g outside q | `∃ g : A, g ∉ q.asIdeal ∧ ...` |
| R→A_g is smooth | `Algebra.Smooth R (Localization.Away g)` |
| W_g is the principal open D(g) inside W, viewed inside X | `iW ''ᵁ PrimeSpectrum.basicOpen g`, an actual member of `X.Opens` |
| Canonical identification W_g≅Spec A_g | The standard localization open immersion has `opensRange = PrimeSpectrum.basicOpen g` by `Scheme.Hom.opensRange_localizationAway`; `Scheme.Hom.opensRange_comp` and `Scheme.Hom.isoOpensRange` identify its composite with iW with exactly the displayed open subscheme. This uses the canonical existing construction, with no arbitrary identification supplied as a hypothesis. |
| The restriction W_g→S is smooth | `Smooth ((iW ''ᵁ PrimeSpectrum.basicOpen g).ι ≫ f)` |
| W_g is an open neighbourhood of x in X | Its openness is part of the type `X.Opens`, and `iW q ∈ iW ''ᵁ PrimeSpectrum.basicOpen g` gives point membership. |

Representing an affine open subscheme by an open immersion from its specified
spectrum is equivalent to giving the open and its affine identification. The
commuting chart square combines the required image containment and the assertion
that φ is the induced map: the unique factor through the open target is
`Spec.map (algebraMap R A)`. It places no additional geometric condition on f.
Using an algebra structure packages an arbitrary ring homomorphism between
commutative rings, and the localization inherits the composite R-algebra structure.
All rings and schemes use the standard common scheme universe u; no test-object
universe is restricted and no finite-presentation hypothesis on R→A is introduced.

Dependency declarations read and reused:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in the
  same Mathlib module. These are the actual affine chart objects and maps.
- `def-weil-pbc-singular-ideal`: `Algebra.IsSmoothAtPrime`, in
  `WeilConjectures.RingTheory.SingularIdeal`; its definition is exactly
  `∃ g, g ∉ q.asIdeal ∧ Algebra.Smooth R (Localization.Away g)`.
- `def-weil-pbc-smooth-ring-map`: `Algebra.Smooth`, in
  `Mathlib.RingTheory.Smooth.Basic`, publicly available through the imports.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Its recorded interface already
  identifies this with the node's lifting notion by Stacks 02H6.

All proof dependencies have usable recorded declarations or Mathlib matches:
`Scheme.isOpenImmersion_SpecMap_localizationAway`,
`Scheme.Hom.opensRange_localizationAway`, `IsOpenImmersion.lift`, `lift_fac`,
`lift_uniq` in `Mathlib.AlgebraicGeometry.OpenImmersion`;
`HasRingHomProperty.Spec_iff` in
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`;
and the smooth open-restriction, composition, open-immersion, and isomorphism
transport interfaces available from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
The four proof steps in the declaration docstring follow the node's four steps
and name each input. The Scheme and algebra-smooth definition modules are exposed
transitively; RingHomProperties has an explicit plain proof import.

Sources checked directly: Stacks `algebra.tex`, definition-smooth-at-prime
(00TB); `more-morphisms.tex`, lemma-smooth-formally-smooth (02H6); and
`morphisms.tex`, lemma-smooth-at-point. The localization-to-open passage uses the
01I3 localization and 01HI open-factor interfaces recorded on the proof nodes.

Edge cases checked before writing:

- A zero chart ring or empty source chart has no `q : PrimeSpectrum A`, so the
  pointwise statement is vacuous, as in the node. No Nontrivial binder is added.
- `g=0` and nilpotent g lie in every prime and cannot satisfy `g ∉ q.asIdeal`;
  their empty principal opens therefore cannot be selected as neighbourhoods.
- `g=1` is permitted, and D(1) is the entire source chart; the statement still
  asserts smoothness over the original target S.
- R→A need not be finitely presented, and f need not be locally of finite
  presentation, quasi-compact, separated, or smooth globally. Only the selected
  localization is required to be smooth. No such extra hypotheses occur.
- The target chart need not equal S: `iV` is an arbitrary open immersion and
  the concluding restricted map has codomain S, exactly as requested.

Searches (all made through the prescribed wrapper unless marked local):

1. LeanFinder: "A ring map smooth at a prime in affine open charts gives a
   principal open neighbourhood smooth over the original scheme target".
   Eight hits, including `Smooth.exists_isStandardSmooth`, `isSmooth_iff`,
   `Algebra.basicOpen_subset_smoothLocus_iff_smooth`, and
   `Algebra.IsSmoothAt.exists_notMem_smooth`. No exact statement. Smooth-locus
   algebra results assume finite presentation of the original algebra; chart
   results start from an already smooth morphism.
2. Loogle: `Algebra.IsSmoothAt.exists_notMem_smooth`. One hit, with the extra
   `[Algebra.FinitePresentation R A]` and formal-stalk `Algebra.IsSmoothAt`.
   This is not the node's principal-localization notion and does not give the
   scheme neighbourhood over the original target.
3. Mathlib grep: `exists_notMem_smooth|isSmooth_iff|smoothLocus_comp`, restricted
   to AlgebraicGeometry. One hit in Morphisms/Smooth.lean, invoking the ring
   finite-presentation lemma; no exact theorem.
4. LeanSearch: "A smooth ring localization on affine charts gives an open
   neighbourhood smooth over the scheme target". Eight hits, all ring
   localization/formal-smoothness or finite-presentation smooth-locus results;
   none states the composite chart neighbourhood assertion.
5. Local `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf`:
   `IsSmoothAtPrime|affineSmoothPrime|smooth.*[Nn]eighbour|smooth.*[Nn]eighbor`.
   Read the existing SingularIdeal definition and related neighbourhood inputs;
   none states this arbitrary-chart result with only principal-localization
   smoothness at q. Also inspected the Artinian-lifting reverse theorem, which
   requires Noetherianity, finite type and an Artinian lifting hypothesis.
6. Local `grep -rn` for this node id in `lean/WeilConjectures`: no hit.
   Local search for the proposed theorem name: no duplicate.

No statement is disputed; no node fault was found.

Validation: the prescribed `scompile.py Q27
lem-trf-affine-smooth-prime-scheme-neighbourhood <module>` compiled the sandbox
and library module separately against the live published build. Both passed in
1.4 seconds with no errors or unexpected warnings. All variables and the one
universe are explicit; `autoImplicit` is false.

## Second reading by Q27

The worker reread the node and the complete module after the successful compile.
This is a second pass by the same worker; the maintainer's delivery review is the
independent reading (the dispatch brief forbids starting other agents).

The two open-immersion binders give precisely the specified affine open charts.
The chart-square equation gives both image containment and the induced ring map,
while the point is parametrized directly by its prime, so `iW q` is exactly x.
The hypothesis uses the recorded `Algebra.IsSmoothAtPrime`, rather than formal
stalk smoothness. The witness retains every required conclusion: g avoids q,
the localized algebra is smooth, the restriction of f to the actual principal
open is smooth over S, and that open contains x. The canonical spectrum/open
identification is the one provided by the localization map and its image, not
an arbitrary isomorphism. It is already built into the chosen principal-open
expression using Mathlib's existing localization/image interfaces. No condition
on finite presentation of the original chart or on global smoothness slipped in.
No mismatch was found and no source or node correction was needed.
