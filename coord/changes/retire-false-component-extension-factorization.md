# AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_factorization

## Reason

Repairs X-f1981 and X-472ac (head 472ace8c7), E2 review point 4, and
X-7c2e9 (head 7c2e9037b), A3/mechanical (d). Aux is claimed on the
project server by B2 as an additional interface-change module; its retirement
is not submitted under the unheld forced-adaptation exception.
STATEMENT-DISPUTED: both the arbitrary-model factorization and the existential Aux
assertions are false. The former is refuted by the retained checked private certificates.
For the latter take R = K = V = F₂, p = (0), the identity local triple t, and the
residue-pointing cocone. For any proposed c and i, put C = c.B and s.B = C × C,
with diagonal structure map, first-coordinate pointing, and β = first projection
followed by i. These satisfy both compatibility equations. Étaleness over a finite
field makes C finite. H = Hom(C,F₂) is finite and nonempty (it contains i, after
identifying the local identity algebra with F₂). The two projection families give
an injection H ⊕ H into Hom(C × C,F₂): evaluation at (r,0) or (0,r) distinguishes
members within one family, and (1,0) distinguishes the two families. Cancellation
along any a would inject H ⊕ H into H by precomposition, an impossibility.
The reviewer's sorry-free finite_field_etale_product_obstruction checks this finite
ring argument. It is copied into scratchpad/ReviewerFiniteFieldProductObstruction.lean
for local validation, not added as a new library statement.

## Old

The first retired declaration:

```lean
theorem etaleResidueTriples_primeLocalization_component_extension_factorization
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (hiα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α)
    (hiφ : i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ) :
    ∃ b : t.B ⟶ V,
      i ≫ b = η.app c ∧
      ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        ∃ a : c ⟶ s,
          (etaleResidueTriplesRingDiagram R p K χ).map a ≫ β = i ∧
          ∀ (f g : s.B ⟶ V),
            (etaleResidueTriplesRingDiagram R p K χ).map a ≫ f =
              (etaleResidueTriplesRingDiagram R p K χ).map a ≫ g → f = g
```


The additional retired Aux declaration, verbatim (its entire docstring is also removed):

```lean
theorem etaleResidueTriples_primeLocalization_component_extension_aux
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃ (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B),
      c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ ∧
      ∃ b : t.B ⟶ V,
        i ≫ b = η.app c ∧
        ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
          s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α →
          β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
            (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
          ∃ a : c ⟶ s,
            (etaleResidueTriplesRingDiagram R p K χ).map a ≫ β = i ∧
            ∀ (f g : s.B ⟶ V),
              (etaleResidueTriplesRingDiagram R p K χ).map a ≫ f =
                (etaleResidueTriplesRingDiagram R p K χ).map a ≫ g → f = g
```

## New

Both false declarations and their original docstrings are removed entirely; there is
no replacement or alias. The factorization module retains its checked private
residuePointingCocone, factorization_counterexample and factorization_statement_refuted
unchanged. The Aux module is empty apart from its unchanged public imports and namespace
scaffolding, with set_option linter.privateModule false after the imports. Both retired
nodes have lean: null and record the counterexamples and retirement.

EtaleResidueTriplesPrimeLocalizationComponentExtensionExists removes its Aux proof import
(original line 5), and replaces the original proof (lines 72–87) with sorry. Its signature,
visibility and entire docstring are unchanged. Its node drops the false Aux dependency and
records the unresolved original existence argument. This is restoration of an existing
obligation, not a new decomposition or a proof.

## Users

Declaration-user audits (downstream.py --uses and rg over both roots) find exactly
Factorization and Aux for the first retired name, and Aux and Exists for the additional
retirement. Aux was the sole direct importer of Factorization; Exists is the sole direct
importer and application site of Aux. Every affected declaration user is listed below.
The 159 transitive downstream modules of Aux require no change because Exists retains
its exact interface. No definition, instance, target signature, or unit route changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxFactorization | B2 | Retire false factorization theorem; retain proved private certificates. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAux | B2 | Reviewer-ordered additional interface retirement: delete the false existential theorem and docstring; remove obsolete AuxModel and AuxFactorization proof imports; retain empty module. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionExists | unclaimed (local claims snapshot) | Forced adaptation: remove Aux proof import and replace invalid proof by existing named hole; signature, visibility and docstring unchanged. |

The original Aux proof fails after factorization retirement with an unknown identifier
etaleResidueTriples_primeLocalization_component_extension_factorization at line 60:4.
The original Exists proof fails after Aux retirement with an unknown identifier
etaleResidueTriples_primeLocalization_component_extension_aux at line 73:4.
The delivery tool checks the unheld Exists original against the changed dependencies;
the adapted modules compile in the delivered set. Aux's additional signature retirement
is expressly required by reviewer X-472ac; it is not an unsolicited caller alteration.

## Status

landed 20261014T084659-L-88460 2026-10-14 (merge of deliver/B2/Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxFactorization)
