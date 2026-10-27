## Worker report

The module `Sheaf.Algebra.Homology.RegularScalarQuotientExactRow` states
`CategoryTheory.RegularScalarQuotient.regularScalarQuotient_exactRow`, with `sorry` as
its entire proof. Its other 20 declarations are transparent abbreviations or real
constructions of the objects and coordinate maps used in the statement. No definition
chooses an object from an existence theorem. No statement correction, new node, or
dependency repair is needed.

The source read was the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`,
paragraph 1. The DAG node is the explicit regular-scalar expansion of its coefficient
calculation, not a verbatim theorem in Bhatt–Scholze. The docstring gives all six proof
steps: repeated cancellation; exact module sheafification; finite free bounded-above
K-flatness; the signed tensor/unit computation; the quotient kernel-image calculation;
and quotient-ring-linear sheafification.

Clause-by-clause rendering:

- An arbitrary site small relative to the coefficient/module universe is
  `{C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}`.
  Object and morphism universes are independent. Coefficients and module sections
  live in universe `r`. Sheaf composition and commutative ring sheafification are
  explicit infrastructure binders; they assert no mathematical restriction on such
  sites. Abelian sheafification is supplied by the recorded K-flat module's instances.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{r}`. `Modules R` is the
  recorded `ringedSiteModules` category with commutativity forgotten. `unit R`
  is Mathlib's regular module. The global section is `t : (unit R).sections`.
- Sectionwise regularity is exactly `hregular : ∀ U : Cᵒᵖ,
  Function.Injective (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) * x)`.
  There is no domain, nonzero-ring, or nonunit hypothesis.
- A natural level `n` denotes paper exponent `n+1`, bijectively covering every
  positive integer exponent. `B R t n` is precisely
  `principalPowerRingQuotient R t (n+1)`: sheafification in commutative rings of
  `R(U)/(t_U^(n+1))`. `projection` is the actual quotient projection, not a supplied
  arbitrary epimorphism. `Q` restricts its regular module along that projection.
- `principalKoszul R t k` is the existing cone of multiplication by `t^(k+1)`
  on the single complex of the regular module, in degrees -1 and 0.
  The first conjunct quantifies over every `k` and supplies its augmentation `ε`
  to `single (Q R t k)`. `IsKFlatResolutionIndependentCoefficients ε` says both
  quasi-isomorphism and K-flatness, using the recorded predicate.
- `koszulRight ... ≫ ε.f 0 = ringMap (projection ...) ≫ singleIn ...`
  pins the augmentation to the quotient in degree zero. The target is single in
  degree zero, so all other components are necessarily zero. The two `Nonempty`
  isomorphisms say its two nonzero degrees are free of rank one, and the last
  `IsZero` clause explicitly states the complex is zero outside {-1,0}.
- `∀ n m, m ≤ n` covers precisely paper `n ≥ m ≥ 1` after shifting both indices.
  The existential ring map `red` is pinned by
  `projection R t n ≫ red = projection R t m`. Thus it is the canonical quotient
  reduction, whose existence and well-definedness are conclusions, not assumptions.
- `P R t n m` is the two-term cone of multiplication by the image of `t^(m+1)`
  on the regular module of `B R t n`; it is a complex of B_n-modules. `tensor`
  uses exactly `CochainComplex.mapBifunctor`, with first factor B_n[0] and second
  factor the existing principal Koszul complex. The chain isomorphism `e` identifies
  it with `restrictedP`, restriction to R of that explicitly B_n-linear cone.
- `tensorIn ... (-1) (koszulLeft ...)` and
  `tensorIn ... 0 (koszulRight ...)` insert `x tensor 1` by the right unitor and
  the actual total-tensor summand inclusions. The two equations for `e.hom.f`
  normalize the identification on both surviving summands. They prevent an
  unspecified chain isomorphism from changing either scalar-coordinate formula.
- The B_n-linear augmentation `ε : P ... ⟶ single ((res red).obj (unit B_m))`
  has its degree-zero coordinate pinned by `rightIn ... ≫ ε.f 0 =
  ringMap red ≫ singleIn ...`. Thus the augmentation of the tensor complex,
  transported by `e` and restriction, is coefficient reduction in degree zero.
  Again all other target degrees are zero.
- `a : (res red).obj (unit B_m) ⟶ unit B_n` is a morphism in `Modules B_n`,
  so its B_n-linearity is part of its type. For every site object and every
  representative `x : R(U)`, its stated equation is exactly
  `a([x]_m) = [t^(n-m)x]_n`. Since quotient sections locally lift from these
  representatives, this characterizes the map on all sections. It is not
  assumed to have any injectivity or exactness property before the conclusion.
- `Mono a` gives exactness at the first nonzero term and `Epi (ringMap red)`
  gives exactness at the last. The two `ShortComplex.Exact` conjuncts give
  exactness at both middle B_n terms. Their zero-composite witnesses are
  existential proof data, not additional hypotheses. All maps are B_n-linear.
- `imageSubobject a = imageSubobject (mul ... (n-m))` identifies the actual
  subobject inside B_n with the image ideal `t^(n-m)B_n`; it states equality
  of subobjects, not merely an unnormalized isomorphism of their objects.
- `∀ h : n = m` explicitly gives identity reduction, the identity formula for
  `a` on every section, and zero middle scalar map. The `eqToHom` expressions
  only transport the equal indices; for reflexivity they are identities.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib's `SheafOfModules`, `unit`, `unitHomEquiv`, abelian instance, and
  `restrictScalars` (the latter in `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; its cochain/quasi-isomorphism conventions are used by
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `ιMapBifunctor`, with `MonoidalCategory.curriedTensor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatResolutionIndependentCoefficients` and
  `IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal` and `cochainModulesPreadditive`, exposing the existing
  independent-universe sheaf tensor; no second tensor is constructed.
- `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients`:
  `principalPowerRingQuotient`, `principalPowerRingProjection` and their sectionwise
  presheaf construction. Added its already-landed owner
  `def-pe-principal-power-ring-quotients` to stmt_deps.
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`: `endoPow`,
  `globalSectionMultiplication`, `principalKoszul`; added its landed owner
  `def-pur-principal-koszul-quotient-towers` to stmt_deps.
- `Sheaf.Algebra.Homology.RegularQuotientConeBasic`:
  `SheafOfModules.RegularQuotientCone.scalar` and `.ringMap`;
  added its landed owner `def-cbc-regular-quotient-cone-basic` to stmt_deps.
- Proof imports retain `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
  (`IsFlatOnSite`), `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (`CochainComplex.isKFlat_of_boundedAbove_flat`),
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`sheafification`, `sheafificationAdjunction`, the finite-limit-preservation
  instance), and `Mathlib.CategoryTheory.Sites.PreservesSheafification`
  (`sheafifyComposeIso`, `sheafComposeIso_hom_fac`). The bounded-flat proof API
  is specialized in universe, but the mathematical proof is transported through
  a small model for the independently sized site, as in the existing K-flat API.

Searches for an exact existing statement:

- msearch LeanFinder: "Sheaf quotient by powers of a regular scalar exact sequence
  and two term Koszul K-flat resolution": 8 hits, chiefly sheaf presentations
  (`SheafOfModules.relationsOfIsCokernelFree`, etc.); none states the quotient row.
- msearch Loogle: `"IsSMulRegular", "exact"`: 3 ordinary-module hits,
  including `IsSMulRegular.smulShortComplex_shortExact`; not the sheaf statement.
- msearch grep: `twoTerm|single.*map|cokernel`, Mathlib Algebra/Homology:
  25 hits, generic complexes and homology. The cone and single APIs are reused.
- msearch LeanSearch: "A regular scalar in a sheaf of commutative rings gives a
  finite free K-flat resolution of its quotient and an exact four term sequence
  of power quotient sheaves": 8 hits, ordinary regular-sequence exactness,
  `RingHom.Flat`, `QuotSMulTop`, and `SheafOfModules.free`; no exact statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for Koszul, scalar quotient,
  regular scalar, and quotient powers found the reusable principal quotient
  rings/Koszul towers, specialized `EllCoefficientFiber`, and scalar cone helpers.
  `EllCoefficientFiber` applies only to completed coefficient sheaves on a scheme;
  it does not give this arbitrary-site regular-scalar row. Exact item-id search
  in WeilConjectures found no attached declaration. Name searches for
  `RegularScalarQuotient`/`regularScalarQuotient_exactRow` in Mathlib, upstream,
  Sheaf and `dag/lean_names_upstream.json` found no collision.

Edge cases checked before writing: n=m gives a=id, red=id and middle map zero;
m=1 is natural level 0; t a unit gives all quotient modules zero; the zero ring
is allowed and regularity is the injectivity of a map on a singleton. No point
or nonempty site is assumed. Cancellation uses no integral-domain hypothesis,
so `(Z/6)[s]` with t=s is included. Empty-site/vacuous-section cases are retained.
No false-statement concern or STATEMENT-DISPUTED flag remains.

Validation: scompile.py compiled the module in both its sandbox and library module
names cleanly (6.8 s and 10.5 s for the final signature at this step). Every variable
and universe is explicitly bound. The sole postponed theorem is the item's main
theorem. No proof or global build was attempted.

## Second reading by Q116

The dispatcher requires a solo worker and forbids starting other agents; this is
my second pass over the node and completed source, with independent review left
to the maintainer as prescribed by the brief. I rechecked each clause against the
source. The only elaboration change needed was an explicit `@id (R.obj.obj U)`
when using `t.val U` as a ring scalar: the type of a section is presented through
the regular module's underlying additive presheaf. This changes no hypothesis.

The rereading checked that the row is typed over B_n, that a's formula uses the
source quotient projection at m and target quotient projection at n, that the
complementary exponent is n-m (unchanged by the +1 index convention), and that
both middle exactness clauses use exponent m+1. It checked that the augmentation
is pinned on the unshifted cone inclusion and that the chain isomorphism is pinned
on both tensor summands. The finite-free clause states rank-one terms at -1,0 and
zero terms elsewhere. At equal levels the conclusion explicitly includes both
identity maps and the zero middle map. No new assumptions, statement changes,
or duplicate underlying notions were found.
