import m154

open m154 (demi_pos)


-- Définition de « u tend vers l »
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
demi_pos : ∀ {ε : ℝ}, ε > 0 → ε / 2 > 0
-/

variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- Si u est constante de valeur l, alors u tend vers l
example : (∀ n, u n = l) → limite_suite u l :=
begin
  Supposons h : ∀ n, u n = l, 
  Soit ε > 0,
  Montrons que ∃ N, ∀ n ≥ N, |u n - l| ≤ ε,
  Montrons que 0 convient : ∀ n ≥ 0, |u n - l| ≤ ε,
  Soit n ≥ 0,
  calc |u n - l| = |l - l| : by On remplace h
             ... = 0 : by On calcule
             ... ≤ ε : by On conclut par ε_pos,
end

/- Concernant les valeurs absolues, on pourra utiliser les lemmes

abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

ineg_triangle (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_diff (x y : ℝ) : |x - y| = |y - x|

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

-- Si u tend vers l strictement positif, alors u n ≥ l/2 pour n assez grand.
example (hl : l > 0) : limite_suite u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  Supposons h : limite_suite u l,
  Par h appliqué à [(l/2), (demi_pos hl)] on obtient N (hN : ∀ n ≥ N, |u n - l| ≤ l / 2),
  Montrons que N convient : ∀ n ≥ N, u n ≥ l / 2,
  Soit n ≥ N,
  Par hN appliqué à [n, (n_ge : n ≥ N)] 
     on obtient hN' : |u n - l| ≤ l / 2,
  On remplace abs_inferieur_ssi dans hN' qui devient -(l / 2) ≤ u n - l ∧ u n - l ≤ l / 2,
  On conclut par hN'.1,
end

/- Concernant le maximum de deux nombres, on pourra utiliser les lemmes

superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

inferieur_max_gauche p q : p ≤ max p q

inferieur_max_droite p q : q ≤ max p q

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

-- Si u tend vers l et v tend vers l' alors u+v tend vers l+l'
example (hu : limite_suite u l) (hv : limite_suite v l') :
limite_suite (u + v) (l + l') :=
begin
  Soit ε > 0,
  Par hu appliqué à [(ε/2), (demi_pos ε_pos)] on obtient N₁ 
      tel que hN₁ : ∀ (n : ℕ), n ≥ N₁ → |u n - l| ≤ ε / 2,
  Par hv appliqué à [(ε/2), (demi_pos ε_pos)] on obtient N₂ 
      tel que hN₂ : ∀ (n : ℕ), n ≥ N₂ → |v n - l'| ≤ ε / 2,
  Montrons que max N₁ N₂ convient,
  Soit n ≥ max N₁ N₂,
  On remplace superieur_max_ssi dans n_ge qui devient n ≥ N₁ ∧ n ≥ N₂,
  Par n_ge on obtient (hn₁ : n ≥ N₁) (hn₂ : n ≥ N₂),
  Fait fait₁ : |u n - l| ≤ ε/2,
    On applique hN₁,
  Fait fait₂ : |v n - l'| ≤ ε/2,
    On conclut par hN₂ appliqué à [n, hn₂],  -- Notez la variante Lean par rapport à fait₁
  calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| : by On calcule
                     ... ≤ |u n - l| + |v n - l'| : by On applique ineg_triangle
                     ... ≤  ε/2 + ε/2             : by On combine [fait₁, fait₂]
                     ... =  ε                     : by On calcule,
end

example (hu : limite_suite u l) (hw : limite_suite w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : limite_suite v l :=
begin
  Soit ε > 0,
  Par hu appliqué à [ε, ε_pos] on obtient N tel que hN : ∀ n ≥ N, |u n - l| ≤ ε,
  Par hw appliqué à [ε, ε_pos] on obtient N' tel que hN' : ∀ n ≥ N', |w n - l| ≤ ε,
  Montrons que max N N' convient,
  Soit n ≥ max N N',
  On remplace superieur_max_ssi dans n_ge,
  Par n_ge on obtient (hn : n ≥ N) (hn' : n ≥ N'),
  Par hN appliqué à [n, hn] on obtient (hN₁ : |u n - l| ≤ ε),
  Par hN' appliqué à [n, hn'] on obtient (hN'₁ : |w n - l| ≤ ε),  
  Par h appliqué à n on obtient h₁ : u n ≤ v n,
  Par h' appliqué à n on obtient h'₁ : v n ≤ w n,
  On remplace abs_inferieur_ssi partout,
  Par hN₁ on obtient (hNl : -ε ≤ u n - l) hNd,
  Par hN'₁ on obtient hN'l (hN'd : w n - l ≤ ε),
  Montrons que -ε ≤ v n - l,
  -- Ici "On combine [ ... ]" peut finir, mais sur papier on écrirait
  calc -ε ≤ u n - l : by On conclut par hNl
      ... ≤ v n - l : by On conclut par h₁,
  Montrons que v n - l ≤ ε,
  calc v n - l ≤ w n - l : by On conclut par h'₁
      ... ≤ ε : by On conclut par hN'd,
end

-- La dernière inégalité dans la définition de limite peut être remplacée par
-- une inégalité stricte.
example (u l) : limite_suite u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  Montrons que limite_suite u l → ∀ ε > 0, (∃ N, ∀ n ≥ N, |u n - l| < ε),
    Supposons hyp : limite_suite u l,
    Soit ε > 0, 
    Par hyp appliqué à [(ε/2), (demi_pos ε_pos)] on obtient N 
        tel que hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2,
    Montrons que N convient,
    Soit n ≥ N,
    calc |u n - l| ≤ ε/2 : by On conclut par hN appliqué à [n, n_ge]
              ...  < ε   : by On conclut par ε_pos,

  Supposons hyp : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε,
  Soit ε > 0,
  Par hyp appliqué à [ε, ε_pos] on obtient N tel que hN : ∀ n ≥ N, |u n - l| < ε,
  Montrons que N convient : ∀ n ≥ N, |u n - l| ≤ ε,
  Soit n ≥ N,
  On conclut par hN appliqué à [n, n_ge],
end

/- Dans l'exercice suivant, on pourra utiliser le lemme

egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y
-/

-- Une suite u admet au plus une limite
example : limite_suite u l → limite_suite u l' → l = l' :=
begin
  Supposons (hl : limite_suite u l) (hl' : limite_suite u l'),
  Par egal_si_abs_eps il suffit de montrer que ∀ (ε : ℝ), ε > 0 → |l - l'| ≤ ε,
  Soit ε > 0,
  Par hl appliqué à [(ε/2), (demi_pos ε_pos)] on obtient N 
      tel que hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2,
  Par hl' appliqué à [(ε/2), (demi_pos ε_pos)] on obtient N' 
      tel que hN' : ∀ (n : ℕ), n ≥ N' → |u n - l'| ≤ ε / 2,
  Par hN appliqué à [(max N N'), (inferieur_max_gauche _ _)]
     on obtient hN₁ : |u (max N N') - l| ≤ ε / 2,
  Par hN' appliqué à [(max N N'), (inferieur_max_droite _ _)]
    on obtient hN'₁ : |u (max N N') - l'| ≤ ε / 2,
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| : by On calcule
  ... ≤ |l - u (max N N')| + |u (max N N') - l'| : by On applique ineg_triangle
  ... =  |u (max N N') - l| + |u (max N N') - l'| : by On remplace abs_diff
  ... ≤ ε/2 + ε/2 : by On combine [hN₁, hN'₁]
  ... = ε : by On calcule,
  /- Alternative en faisant disparaître les valeurs absolues 
  On remplace abs_inferieur_ssi partout,
  Montrons que -ε ≤ l - l',
  On combine [hN₁, hN'₁],
  Montrons que l - l' ≤ ε,
  On combine [hN₁, hN'₁], -/
end

-- Définition de « la suite u est croissante »
def croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- Définition de « M est borne supérieure des termes de la suite u  »
def est_borne_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- Toute suite croissante ayant une borne supérieure tend vers cette borne
example (M : ℝ) (h : est_borne_sup M u) (h' : croissante u) :
limite_suite u M :=
begin
  Soit ε > 0,
  Par h on obtient (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε),
  Par sup_M_ep appliqué à [ε, ε_pos] on obtient n₀ tel que hn₀ : u n₀ ≥ M - ε,
  Montrons que n₀ convient : ∀ n ≥ n₀, |u n - M| ≤ ε,
  Soit n ≥ n₀,
  On remplace abs_inferieur_ssi,
  Montrons que -ε ≤ u n - M,
    Par h' appliqué à [n₀, n, n_ge] on obtient h'' : u n₀ ≤ u n,
    On combine [h'', hn₀],
  Montrons que u n - M ≤ ε,
  Par inf_M appliqué à n on obtient inf_M' : u n ≤ M,
  On combine [inf_M', ε_pos],
end
