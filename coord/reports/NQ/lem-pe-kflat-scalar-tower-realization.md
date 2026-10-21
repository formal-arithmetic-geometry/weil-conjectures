## Worker report

Item: `lem-pe-kflat-scalar-tower-realization`. Module:
`Sheaf.Algebra.Homology.KFlatScalarTowerRealization`.
Primary declaration:
`SheafOfModules.KFlatScalarTower.kflat_scalar_tower_realization`.
This is a stage-2 statement, with its sole theorem proof `by sorry`.
All helper definitions have actual data. No node statement or dependency was changed.

The module uses the already recorded `SuccessiveDerivedQuotient.Presentation` and
`Normalization`, rather than making another choice of scalar extension or adjunction.
The parameters `p` and `N` denote the functors and normalized structures stipulated in
the node. Their existence is the recorded
`successive_derived_quotient_normalization`. Quantification over these presentations
keeps their canonical counits visible and does not assume a new arbitrary comparison.
`Modules` is the dependency's abbreviation for `ringedSiteModules`, itself exactly
Mathlib's `SheafOfModules`. Scalar-first notation `s tensor x` represents the paper's
`x tensor s`.

Hypotheses and objects:

| Node text | Lean rendering |
| --- | --- |
| Site small in the module universe | `C : Type u`, `Category.{v} C`, `EssentiallySmall.{r} C`, topology `J`; standard ring-forgetting/sheafification/locally-bijective instances are explicit. Site object and morphism universes remain independent. |
| Ring sheaf R, coefficient ring sheaves B_n | `R : Sheaf J CommRingCat.{r}`, `B : ℕ → Sheaf J CommRingCat.{r}`. Lean index n means paper index n+1. |
| Maps a_n, b_n and b_n a_(n+1) = a_n | Binders `a`, `b`, `h`, with `a (n+1) ≫ b n = a n`. |
| Unbounded module derived categories and Q | `DerivedCategory (Modules R)` and analogous categories; the common chosen derived Hom universe is `w`, with its `HasDerivedCategory` family. `localize` is `quotient ⋙ Qh`, canonically the localization `Q` by `DerivedCategory.quotientCompQhIso`. This is the same localization expressed in the dependency's homotopy interface. |
| F_n, G_n and restrictions r_n, j_n | `(p (a n)).derived`, `(p (b n)).derived`, `N.right (a n)`, `N.right (b n)`; `derivedEnd` abbreviates F_n followed by r_n. |
| Normalized adjunction units | `N.adjunction`; its ordinary and derived unit normalizations are fields of the recorded `Normalization`. |
| Canonical alpha and its restricted adjunct d_n | `derivedStep` first uses the unit for b, then `N.derived`, transports along h, restricts along a, and applies `N.rightComp` and h. This is the explicit unit formula for the adjoint of alpha, not a freely chosen arrow. |
| Flat-term K-flat P | `P : CochainComplex (Modules R) ℤ`, `hP : IsKFlatIndependentCoefficients P`, `hf : ∀ i, IsFlatOnSite (P.X i)`. |
| Arbitrary K and representative isomorphism e | `K : DerivedCategory (Modules R)`, `e : (localize R).obj P ≅ K`. |
| Strict T_n(P) | `((ordinaryEnd p (a n)).mapHomologicalComplex (.up ℤ)).obj P`; ordinaryEnd is the existing scalar extension followed by the existing scalar restriction. |
| Strict c_n | Termwise image of `(N.ordinaryAdjunction (a n)).unit`, which `N.ordinary_unit` identifies on every section with `x ↦ 1 tensor x`. |
| Strict t_n | Termwise image of `ordinaryStep`; the theorem explicitly identifies its sections with `s tensor x ↦ b_n(s) tensor x`. |
| Canonical epsilon_n | `epsilon` is `derivedEnd.map e.inv ≫ computation`. `computation` is restriction of the universal derived counit, followed by `N.right_factors` and the standard mapHomotopyCategory composition isomorphism. It is fixed before the theorem. |

Conclusion, conjunct by conjunct in file order:

1. `∀ n, IsIso (epsilon ...)` gives the asserted canonical comparison isomorphisms.
   An invertible specified morphism is equivalent to an isomorphism with that hom.
2. `e.hom ≫ unit ≫ epsilon = localize.map c` is exactly
   epsilon_n composed with u_n(K) composed with e equals Q(c_n).
3. `derivedStep.app K ≫ epsilon_n = epsilon_(n+1) ≫ localize.map t_n`
   is exactly the adjacent transition square, in Lean's left-to-right composition.
4. The sectionwise equality for `ordinaryStep.app (P.X i)` spells out the strict
   tensor transition in every degree and on every site object.
5. `c_(n+1) ≫ t_n = c_n` records the strict augmentation compatibility.
6. For every second flat-term K-flat representative P', e', chain map f, and derived
   map g with `Q(f) ≫ e'.hom = e.hom ≫ g`, the displayed epsilon square gives the
   asserted naturality, including identities and arbitrary representative transports.
   Naturality of strict maps also follows directly from their construction as natural
   transformations, mapped termwise; it is not replaced by an existence hypothesis.
7. The equation using `composite` gives the comparison square for every n ≤ m.
   `composite` evaluates Mathlib's `Functor.ofOpSequence` at the order morphism, so
   this includes m=n and arbitrary lengths, not just two successive quotients.
8. For every n ≤ m the final existential proves the ring compatibility `hc` and
   identifies both the direct derived mate and the direct strict chain map for
   `B_m → B_n` with their respective iterated adjacent composites. `hc` is a proof
   in the conclusion, not an extra assumption supplied by a caller.

Dependency declarations used (read their signatures and docstrings):

- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`,
  `NatTrans.ofOpSequence` (the former implements the finite composites).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exposed by the `Modules` abbreviation in the scalar-composition dependency.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Qh`, `quotientCompQhIso`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`;
  the universal-pair notion used through `Presentation` is the same ordinary
  scalar extension with its universal counit. The recorded module is imported.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used through `restriction`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `sheafRingDerivedCoefficientAdjunction`; its normalized data are exposed by
  `Normalization.ordinaryAdjunction`, `ordinary_unit`, `adjunction`,
  `adjunction_normalization`, `right_factors` in the next dependency.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `Presentation`, `Normalization`, `sectionTensor`, `restriction`, `Modules`,
  `successive_derived_quotient_normalization`. In particular `ordinary`, `derived`,
  `restrictionComp`, and `rightComp` are the prescribed canonical comparisons;
  their section and representative clauses prevent arbitrary isomorphisms.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded tensor module, using the existing sheafified tensor and supporting
  its independent site universes. Ordinary scalar extension itself is fixed by
  `Presentation.obj_eq` and `map_eq` to `changeOfRings` and `changeOfRingsHom`.
- The proof dependency `Sheaf.Paper.KFlatRingedToposPullback` is imported for
  flat-term K-flat preservation, following proof step 4 of the node.

Edge cases checked before/following drafting: zero P and zero coefficient sheaves;
identity coefficient maps and repetitions in the tower; first index n=0; equal
indices m=n (the identity morphism in ofOpSequence); arbitrary finite lengths;
nonflat/nonsurjective coefficient maps; unbounded P; arbitrary choices of e and
arbitrary compatible chain maps. There is no nontriviality, flatness of ring maps,
surjectivity or boundedness binder. The chosen coefficient/module universe r is
independent of the site's object and morphism universes u and v; no equality of
those universes is imposed. There is no disputed statement or source correction.

Searches performed using the prescribed `msearch.py NQ <item>` wrapper:

- LeanFinder: `K-flat realization of a tower of derived scalar extensions compatible
  with adjunction units and quotient transitions`. Eight hits, including
  `comonadicExtendScalars`, `Module.Flat.trans`, and ordinary scalar-extension
  exactness; none state this canonical augmented tower comparison.
- Loogle: `"derived", "unit"`. Twelve hits for general left/right derived counits
  and units; none give the simultaneous tower, augmentation, and transition result.
- Mathlib grep: `kFlat.*(unit|transition)|[Kk]Flat.*[Cc]omparison|scalarTower`.
  Twenty-five returned hits concerned ordinary algebraic scalar towers and unrelated
  flatness statements, not the item.
- LeanSearch: `Canonical K-flat computation of derived scalar extension compatible
  with units and all transitions in a ring sheaf tower`. Eight hits on ordinary
  module flatness and scalar towers; no exact match.
- Project/source `rg`: `lem-pe-kflat-scalar-tower-realization|scalarTower|ScalarTowerRealization`
  in `lean/WeilConjectures` and `lean/Sheaf`. No existing declaration for this node;
  unrelated scalar towers and semilinear comparisons were returned.
- Name-clash `rg` in the same trees and `dag/lean_names_upstream.json`:
  `KFlatScalarTower|kflat_scalar_tower_realization|ordinaryStep|derivedStep`.
  Only differently namespaced pro-etale derivedStep declarations were found.

Sources opened: the full item and dependency node records; the recorded source
interfaces; Stacks sites-cohomology.tex, lemma-derived-base-change and
lemma-derived-pullback-composition. The latter computes both successive pullbacks
on a flat-term K-flat representative and supplies precisely the comparison used
in the node. No new independent mathematical notion was needed.

Validation: prescribed scompile.py only, separately compiling this single module
in sandbox and library-name modes. The initial elaboration errors (noncomputable
abbreviation and inference of a dependent sequence family) were repaired without
changing the mathematical statement. Delivery preflight and the final per-file
compile are run through deliver2.py.

## Second reading by NQ

I reopened the node and the complete final module for a separate clause-by-clause
pass. No sub-agent was started, as the dispatcher brief forbids other agents.
The table and numbered clauses above record that reading. The inverse of e is
used in epsilon, and both augmentation and transition equalities have the correct
composition order and correct source/target. The ordinary and derived transitions
are the adjoint of the canonical scalar-composition comparison, not arbitrary
maps. In particular h transports both the presented extension and the restriction
comparison to a_n.

The second pass checked the often omitted final clause: an adjacent square alone
would not explicitly identify the direct transition for a composite ring map.
The final conjunct now states that identification for both strict and derived
maps and for every n ≤ m, with m=n retained. The strict tensor section formula and
strict augmentation identity are explicit. Naturality allows arbitrary f and all
e, e', rather than just identical representative choices. IsIso is asserted of the
predefined canonical morphism, so a mere existence of unrelated isomorphisms cannot
satisfy the statement. All definitions are fully written, and the only postponed
proof is the named theorem of this node. No mismatch remains.
