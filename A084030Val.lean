import Mathlib
import A084030

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-!
# A084030Val : objet fonctionnel "diagonale de A084029"

Module livre (promotion du correctif D2+, audit
`STATUS/D2PLUS/A084030.md` : VERDICT FAIL corrige, rapport
`STATUS/D2PLUS/A084030-FIX.md`, run CI `43043192525`). Les
theoremes du module eponyme prouvent la cardinalite des lignes
(`A084030`, `A084030_zero_unique`, `A084030_one`) mais le
terme diagonal `T(n,n)` n'etait pas extrait en objet kernel.
Ce module ajoute l'objet-suite du %N « Main diagonal of
triangle A084029 » :

Verbatim OEIS (A084030, offset 1,3) : "Main diagonal of triangle A084029".
A084029 T(n,k) = k-ieme plus petit nombre a n chiffres, multiple de n, de
somme de chiffres n (0 si la ligne a moins de k termes). Donc a(n) =
T(n,n) = le n-ieme plus petit temoin de la ligne n, ou 0 si la ligne
n'a pas n termes.

Contenu :

- `Tdiag n` : l'ensemble des temoins de la ligne n precedes d'au moins
  n-1 temoins strictement plus petits (positions >= n en ordre
  croissant) ;
- `a084030_val n = sInf (Tdiag n)` : le n-ieme temoin (= le terme
  diagonal), 0 si l'ensemble est vide - exactement la convention
  "0 si moins de n termes" de la fiche ;
- `a084030_val_eq` : certificat de position - si v est temoin avec
  exactement n-1 temoins plus petits, a(n) = v ;
- ancres a(n) = v pour n = 1..16 contre la fiche (les n-1 elements
  plus petits certifies par listes explicites + `decide` kernel-pur
  sur les multiples de la fenetre [10^(n-1), v)) ;
- `a084030_val 2 = 0` (Tdiag 2 vide : un seul temoin 20, pas de
  deuxieme element) ;
- conjecture %C portee sur l'objet : `a084030_val n = 0 <-> n = 2`
  pour n >= 1 ("only one term is zero") via `card_witnesses_ge` +
  selection d'un sous-ensemble de cardinal n + lemme de position
  du maximum.

Kernel-pur : `decide` / `sInf` / `Finset` ; aucun `sorry`,
`admit`, `native_decide`, `ofReduceBool`. La table de temoins
du parent (`table029_ok_all`, plage [3,130]) est certifiee
par morceaux `decide +kernel` dans les modules
`Scratch029_cert_*` : la chaine entiere ne depend que des
trois axiomes standards.
-/

open A084030

namespace A084030Val

/-- Candidats au terme diagonal : temoins de la ligne n precedes d'au
    moins n-1 temoins strictement plus petits, i.e. positions >= n. -/
def Tdiag (n : ℕ) : Set ℕ :=
  {v | v ∈ witnesses n ∧
      n - 1 ≤ ((witnesses n).filter (· < v)).card}

/-- a(n) = T(n,n) : le n-ieme plus petit temoin de la ligne n,
    0 par convention sInf si la ligne a moins de n termes. -/
noncomputable def a084030_val (n : ℕ) : ℕ := sInf (Tdiag n)

/-- Certificat de position : v temoin avec exactement n-1 temoins
    strictement plus petits est le terme diagonal. -/
theorem a084030_val_eq {n v : ℕ} (hv : v ∈ witnesses n)
    (hcard : ((witnesses n).filter (· < v)).card = n - 1) :
    a084030_val n = v := by
  have hvT : v ∈ Tdiag n := ⟨hv, le_of_eq hcard.symm⟩
  have hmin : ∀ y ∈ Tdiag n, v ≤ y := by
    intro y hy
    rcases hy with ⟨hys, hycard⟩
    by_contra hlt
    push_neg at hlt
    -- y < v : alors {x < y} ++ {y} ⊆ {x < v} -> card{<y} + 1 <= card{<v}
    have hymem : y ∈ (witnesses n).filter (· < v) :=
      Finset.mem_filter.2 ⟨hys, hlt⟩
    have hsub : (witnesses n).filter (· < y)
        ⊆ (witnesses n).filter (· < v) := fun z hz =>
      Finset.mem_filter.2 ⟨Finset.mem_filter.1 hz |>.1,
        lt_trans (Finset.mem_filter.1 hz |>.2) hlt⟩
    have hnot : y ∉ (witnesses n).filter (· < y) :=
      fun hm => (lt_irrefl y) (Finset.mem_filter.1 hm |>.2)
    have hcardle : ((witnesses n).filter (· < y)).card + 1
        ≤ ((witnesses n).filter (· < v)).card := by
      have h1 : ((witnesses n).filter (· < y)).card
          ≤ (((witnesses n).filter (· < v)).erase y).card :=
        Finset.card_le_card fun z hz => Finset.mem_erase.2
          ⟨ne_of_lt (Finset.mem_filter.1 hz |>.2), hsub hz⟩
      rw [Finset.card_erase_of_mem hymem] at h1
      have hpos : 0 < ((witnesses n).filter (· < v)).card :=
        Finset.card_pos.2 ⟨y, hymem⟩
      omega
    omega
  apply le_antisymm (Nat.sInf_le hvT)
  exact hmin _ (Nat.sInf_mem ⟨v, hvT⟩)

/-- Ligne 2 : le seul temoin est 20. -/
private theorem wit030_2 : witnesses 2 = {20} := by decide

/-- Tdiag 2 est vide : un seul temoin (20), aucun n'a 1 temoin plus
    petit -> a(2) = 0, le zero-padding de la fiche. -/
private theorem tdiag2_empty : Tdiag 2 = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun v hv => by
    rcases hv with ⟨hvw, hcard⟩
    rw [wit030_2] at hvw hcard
    rw [Finset.mem_singleton] at hvw
    subst hvw
    exact absurd hcard (by decide)

/-- a(2) = 0 : le terme nul de la suite (conjecture %C, cas de base). -/
theorem a084030_val_two : a084030_val 2 = 0 := by
  unfold a084030_val
  rw [tdiag2_empty]
  exact Nat.sInf_eq_zero.mpr (Or.inr rfl)

/-- Non-vacuite pour n >= 3 : n temoins (fournis par
    `card_witnesses_ge`) ont un maximum qui possede >= n-1 temoins
    plus petits. -/
theorem tdiag_nonempty (n : ℕ) (hn : 3 ≤ n) : (Tdiag n).Nonempty := by
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (card_witnesses_ge n hn)
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    omega
  have hMmem : T.max' hTne ∈ witnesses n := hTsub (Finset.max'_mem _ _)
  have hMsmall : n - 1
      ≤ ((witnesses n).filter (· < T.max' hTne)).card := by
    have hsub : T.erase (T.max' hTne)
        ⊆ (witnesses n).filter (· < T.max' hTne) := by
      intro x hx
      rcases Finset.mem_erase.1 hx with ⟨hxne, hxT⟩
      exact Finset.mem_filter.2 ⟨hTsub hxT,
        lt_of_le_of_ne (Finset.le_max' _ _ hxT) hxne⟩
    calc n - 1 = (T.erase (T.max' hTne)).card := by
          rw [Finset.card_erase_of_mem (Finset.max'_mem _ _), hTcard]
      _ ≤ ((witnesses n).filter (· < T.max' hTne)).card :=
          Finset.card_le_card hsub
  exact ⟨T.max' hTne, hMmem, hMsmall⟩

/-- a(n) > 0 pour n >= 3 : le terme diagonal est un temoin a n chiffres. -/
theorem a084030_val_pos (n : ℕ) (hn : 3 ≤ n) : 0 < a084030_val n := by
  obtain ⟨M, hMem⟩ := tdiag_nonempty n hn
  have hmem : a084030_val n ∈ Tdiag n := Nat.sInf_mem ⟨M, hMem⟩
  have hlen := (Finset.mem_filter.1 hmem.1).2.2.1
  rcases Nat.eq_zero_or_pos (a084030_val n) with h0 | hpos
  · rw [h0, Nat.digits_zero] at hlen; simp at hlen; omega
  · exact hpos

/-- a(1) = 1 : seul temoin de la ligne 1. -/
theorem a084030_val_one : a084030_val 1 = 1 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  decide

/-- Conjecture %C sur l'objet extrait : "only one term is zero" -
    pour n >= 1, a(n) = 0 ssi n = 2. PROUVE. -/
theorem a084030_val_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    a084030_val n = 0 ↔ n = 2 := by
  constructor
  · intro h
    by_cases h2 : n = 2
    · exact h2
    · by_cases h1 : n = 1
      · rw [h1, a084030_val_one] at h; exact absurd h (by decide)
      · have h3 : 3 ≤ n := by omega
        exact absurd h (ne_of_gt (a084030_val_pos n h3))
  · intro h; rw [h]; exact a084030_val_two

/-! ## Ancres a(n) = terme OEIS, n = 3..16

Pour chaque n : la liste L des n-1 temoins strictement plus petits est
certifiee complete par un `decide` sur les multiples de n de la fenetre
couvrant [10^(n-1), v), puis `a084030_val_eq` conclut. -/

-- n = 3 : a(3) = 120 ; petits : {102, 111}
private theorem c030_3 : ∀ j < 7,
    (Nat.digits 10 (3 * (j + 33))).length = 3
    ∧ (Nat.digits 10 (3 * (j + 33))).sum = 3
    → 3 * (j + 33) ∈ [102, 111] := by decide

private theorem w3sm : (witnesses 3).filter (· < 120)
    = [102, 111].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 3 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (3 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 2 ≤ 10 * (3 * j) := h1
    have hlow : 100 ≤ 3 * j := Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 33 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 3 * 33 ≤ 3 * j) (by norm_num)
    have hc := c030_3 (j - 33) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_3 : a084030_val 3 = 120 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w3sm]; decide

-- n = 4 : a(4) = 2020 ; petits : {1012, 1120, 1300}
private theorem c030_4 : ∀ j < 255,
    (Nat.digits 10 (4 * (j + 250))).length = 4
    ∧ (Nat.digits 10 (4 * (j + 250))).sum = 4
    → 4 * (j + 250) ∈ [1012, 1120, 1300] := by decide

private theorem w4sm : (witnesses 4).filter (· < 2020)
    = [1012, 1120, 1300].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 4 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (4 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 3 ≤ 10 * (4 * j) := h1
    have hlow : 1000 ≤ 4 * j := Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 250 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 4 * 250 ≤ 4 * j) (by norm_num)
    have hc := c030_4 (j - 250) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_4 : a084030_val 4 = 2020 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w4sm]; decide

-- n = 5 : a(5) = 10400 ; petits : {10040, 10130, 10220, 10310}
private theorem c030_5 : ∀ j < 80,
    (Nat.digits 10 (5 * (j + 2000))).length = 5
    ∧ (Nat.digits 10 (5 * (j + 2000))).sum = 5
    → 5 * (j + 2000) ∈ [10040, 10130, 10220, 10310] := by decide

private theorem w5sm : (witnesses 5).filter (· < 10400)
    = [10040, 10130, 10220, 10310].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 5 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (5 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 4 ≤ 10 * (5 * j) := h1
    have hlow : 10000 ≤ 5 * j := Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 2000 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 5 * 2000 ≤ 5 * j) (by norm_num)
    have hc := c030_5 (j - 2000) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_5 : a084030_val 5 = 10400 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w5sm]; decide

-- n = 6 : a(6) = 100140 ; petits :
-- {100014, 100032, 100050, 100104, 100122}
private theorem c030_6 : ∀ j < 24,
    (Nat.digits 10 (6 * (j + 16666))).length = 6
    ∧ (Nat.digits 10 (6 * (j + 16666))).sum = 6
    → 6 * (j + 16666) ∈ [100014, 100032, 100050, 100104, 100122] := by
  decide

private theorem w6sm : (witnesses 6).filter (· < 100140)
    = [100014, 100032, 100050, 100104, 100122].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 6 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (6 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 5 ≤ 10 * (6 * j) := h1
    have hlow : 100000 ≤ 6 * j := Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 16666 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 6 * 16666 ≤ 6 * j) (by norm_num)
    have hc := c030_6 (j - 16666) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_6 : a084030_val 6 = 100140 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w6sm]; decide

-- n = 7 : a(7) = 1001203 ; petits :
-- {1000006, 1000132, 1000321, 1000510, 1001014, 1001140}
private theorem c030_7 : ∀ j < 172,
    (Nat.digits 10 (7 * (j + 142857))).length = 7
    ∧ (Nat.digits 10 (7 * (j + 142857))).sum = 7
    → 7 * (j + 142857) ∈
      [1000006, 1000132, 1000321, 1000510, 1001014, 1001140] := by decide

private theorem w7sm : (witnesses 7).filter (· < 1001203)
    = [1000006, 1000132, 1000321, 1000510, 1001014, 1001140].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 7 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (7 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 6 ≤ 10 * (7 * j) := h1
    have hlow : 1000000 ≤ 7 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 142857 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 7 * 142857 ≤ 7 * j)
        (by norm_num)
    have hc := c030_7 (j - 142857) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_7 : a084030_val 7 = 1001203 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w7sm]; decide

-- n = 8 : a(8) = 10001312 ; petits :
-- {10000016, 10000160, 10000232, 10000304, 10000520, 10001024, 10001240}
private theorem c030_8 : ∀ j < 164,
    (Nat.digits 10 (8 * (j + 1250000))).length = 8
    ∧ (Nat.digits 10 (8 * (j + 1250000))).sum = 8
    → 8 * (j + 1250000) ∈ [10000016, 10000160, 10000232, 10000304,
      10000520, 10001024, 10001240] := by decide

private theorem w8sm : (witnesses 8).filter (· < 10001312)
    = [10000016, 10000160, 10000232, 10000304, 10000520, 10001024,
      10001240].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 8 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (8 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 7 ≤ 10 * (8 * j) := h1
    have hlow : 10000000 ≤ 8 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 1250000 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 8 * 1250000 ≤ 8 * j)
        (by norm_num)
    have hc := c030_8 (j - 1250000) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_8 : a084030_val 8 = 10001312 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w8sm]; decide

-- n = 9 : a(9) = 100000080 ; petits : 8 termes
private theorem c030_9 : ∀ j < 9,
    (Nat.digits 10 (9 * (j + 11111111))).length = 9
    ∧ (Nat.digits 10 (9 * (j + 11111111))).sum = 9
    → 9 * (j + 11111111) ∈ [100000008, 100000017, 100000026, 100000035,
      100000044, 100000053, 100000062, 100000071] := by decide

private theorem w9sm : (witnesses 9).filter (· < 100000080)
    = [100000008, 100000017, 100000026, 100000035, 100000044, 100000053,
      100000062, 100000071].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 9 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (9 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 8 ≤ 10 * (9 * j) := h1
    have hlow : 100000000 ≤ 9 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 11111111 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 9 * 11111111 ≤ 9 * j)
        (by norm_num)
    have hc := c030_9 (j - 11111111) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_9 : a084030_val 9 = 100000080 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w9sm]; decide

-- n = 10 : a(10) = 1000000900 ; petits : 9 termes
private theorem c030_10 : ∀ j < 90,
    (Nat.digits 10 (10 * (j + 100000000))).length = 10
    ∧ (Nat.digits 10 (10 * (j + 100000000))).sum = 10
    → 10 * (j + 100000000) ∈ [1000000090, 1000000180, 1000000270,
      1000000360, 1000000450, 1000000540, 1000000630, 1000000720,
      1000000810] := by decide

private theorem w10sm : (witnesses 10).filter (· < 1000000900)
    = [1000000090, 1000000180, 1000000270, 1000000360, 1000000450,
      1000000540, 1000000630, 1000000720, 1000000810].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 10 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (10 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 9 ≤ 10 * (10 * j) := h1
    have hlow : 1000000000 ≤ 10 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 100000000 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 10 * 100000000 ≤ 10 * j)
        (by norm_num)
    have hc := c030_10 (j - 100000000) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_10 : a084030_val 10 = 1000000900 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w10sm]; decide

-- n = 11 : a(11) = 10000010108 ; petits : 10 termes
private theorem c030_11 : ∀ j < 919,
    (Nat.digits 10 (11 * (j + 909090909))).length = 11
    ∧ (Nat.digits 10 (11 * (j + 909090909))).sum = 11
    → 11 * (j + 909090909) ∈ [10000000109, 10000000208, 10000000307,
      10000000406, 10000000505, 10000000604, 10000000703, 10000000802,
      10000000901, 10000010009] := by decide

private theorem w11sm : (witnesses 11).filter (· < 10000010108)
    = [10000000109, 10000000208, 10000000307, 10000000406, 10000000505,
      10000000604, 10000000703, 10000000802, 10000000901,
      10000010009].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 11 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (11 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 10 ≤ 10 * (11 * j) := h1
    have hlow : 10000000000 ≤ 11 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 909090909 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 11 * 909090909 ≤ 11 * j)
        (by norm_num)
    have hc := c030_11 (j - 909090909) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_11 : a084030_val 11 = 10000010108 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w11sm]; decide

-- n = 12 : a(12) = 100000000524 ; petits : 11 termes
private theorem c030_12 : ∀ j < 44,
    (Nat.digits 10 (12 * (j + 8333333333))).length = 12
    ∧ (Nat.digits 10 (12 * (j + 8333333333))).sum = 12
    → 12 * (j + 8333333333) ∈ [100000000056, 100000000092,
      100000000128, 100000000164, 100000000236, 100000000272,
      100000000308, 100000000344, 100000000380, 100000000416,
      100000000452] := by decide

private theorem w12sm : (witnesses 12).filter (· < 100000000524)
    = [100000000056, 100000000092, 100000000128, 100000000164,
      100000000236, 100000000272, 100000000308, 100000000344,
      100000000380, 100000000416, 100000000452].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 12 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (12 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 11 ≤ 10 * (12 * j) := h1
    have hlow : 100000000000 ≤ 12 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 8333333333 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 12 * 8333333333 ≤ 12 * j)
        (by norm_num)
    have hc := c030_12 (j - 8333333333) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_12 : a084030_val 12 = 100000000524 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w12sm]; decide

-- n = 13 : a(13) = 1000000002235 ; petits : 12 termes
private theorem c030_13 : ∀ j < 172,
    (Nat.digits 10 (13 * (j + 76923076923))).length = 13
    ∧ (Nat.digits 10 (13 * (j + 76923076923))).sum = 13
    → 13 * (j + 76923076923) ∈ [1000000000129, 1000000000246,
      1000000000363, 1000000000480, 1000000000714, 1000000000831,
      1000000001065, 1000000001182, 1000000001416, 1000000001533,
      1000000001650, 1000000002118] := by decide

private theorem w13sm : (witnesses 13).filter (· < 1000000002235)
    = [1000000000129, 1000000000246, 1000000000363, 1000000000480,
      1000000000714, 1000000000831, 1000000001065, 1000000001182,
      1000000001416, 1000000001533, 1000000001650,
      1000000002118].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 13 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (13 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 12 ≤ 10 * (13 * j) := h1
    have hlow : 1000000000000 ≤ 13 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 76923076923 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 13 * 76923076923 ≤ 13 * j)
        (by norm_num)
    have hc := c030_13 (j - 76923076923) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_13 : a084030_val 13 = 1000000002235 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w13sm]; decide

-- n = 14 : a(14) = 10000000002650 ; petits : 13 termes
private theorem c030_14 : ∀ j < 190,
    (Nat.digits 10 (14 * (j + 714285714285))).length = 14
    ∧ (Nat.digits 10 (14 * (j + 714285714285))).sum = 14
    → 14 * (j + 714285714285) ∈ [10000000000256, 10000000000382,
      10000000000508, 10000000000634, 10000000000760, 10000000001138,
      10000000001264, 10000000001390, 10000000001516, 10000000001642,
      10000000002146, 10000000002272, 10000000002524] := by decide

private theorem w14sm : (witnesses 14).filter (· < 10000000002650)
    = [10000000000256, 10000000000382, 10000000000508, 10000000000634,
      10000000000760, 10000000001138, 10000000001264, 10000000001390,
      10000000001516, 10000000001642, 10000000002146, 10000000002272,
      10000000002524].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 14 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (14 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 13 ≤ 10 * (14 * j) := h1
    have hlow : 10000000000000 ≤ 14 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 714285714285 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 14 * 714285714285 ≤ 14 * j)
        (by norm_num)
    have hc := c030_14 (j - 714285714285) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_14 : a084030_val 14 = 10000000002650 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w14sm]; decide

-- n = 15 : a(15) = 100000000000950 ; petits : 14 termes
private theorem c030_15 : ∀ j < 64,
    (Nat.digits 10 (15 * (j + 6666666666666))).length = 15
    ∧ (Nat.digits 10 (15 * (j + 6666666666666))).sum = 15
    → 15 * (j + 6666666666666) ∈ [100000000000095, 100000000000185,
      100000000000275, 100000000000365, 100000000000455,
      100000000000545, 100000000000590, 100000000000635,
      100000000000680, 100000000000725, 100000000000770,
      100000000000815, 100000000000860, 100000000000905] := by decide

private theorem w15sm : (witnesses 15).filter (· < 100000000000950)
    = [100000000000095, 100000000000185, 100000000000275,
      100000000000365, 100000000000455, 100000000000545,
      100000000000590, 100000000000635, 100000000000680,
      100000000000725, 100000000000770, 100000000000815,
      100000000000860, 100000000000905].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 15 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (15 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 14 ≤ 10 * (15 * j) := h1
    have hlow : 100000000000000 ≤ 15 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 6666666666666 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 15 * 6666666666666 ≤ 15 * j)
        (by norm_num)
    have hc := c030_15 (j - 6666666666666) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_15 : a084030_val 15 = 100000000000950 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w15sm]; decide

-- n = 16 : a(16) = 1000000000003408 ; petits : 15 termes
private theorem c030_16 : ∀ j < 213,
    (Nat.digits 10 (16 * (j + 62500000000000))).length = 16
    ∧ (Nat.digits 10 (16 * (j + 62500000000000))).sum = 16
    → 16 * (j + 62500000000000) ∈ [1000000000000096, 1000000000000384,
      1000000000000528, 1000000000000672, 1000000000000816,
      1000000000000960, 1000000000001248, 1000000000001392,
      1000000000001536, 1000000000001680, 1000000000001824,
      1000000000002256, 1000000000002544, 1000000000002832,
      1000000000003264] := by decide

private theorem w16sm : (witnesses 16).filter (· < 1000000000003408)
    = [1000000000000096, 1000000000000384, 1000000000000528,
      1000000000000672, 1000000000000816, 1000000000000960,
      1000000000001248, 1000000000001392, 1000000000001536,
      1000000000001680, 1000000000001824, 1000000000002256,
      1000000000002544, 1000000000002832, 1000000000003264].toFinset := by
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_filter.1 hx with ⟨hxw, hxv⟩
    rcases Finset.mem_filter.1 hxw with ⟨-, hdvd, hlen, hsum⟩
    obtain ⟨j, rfl⟩ := hdvd
    have hx0 : 16 * j ≠ 0 := by
      intro h0; rw [h0, Nat.digits_zero] at hlen; simp at hlen
    have h1 := Nat.base_pow_length_digits_le 10 (16 * j) (by norm_num) hx0
    rw [hlen] at h1
    have h1' : 10 * 10 ^ 15 ≤ 10 * (16 * j) := h1
    have hlow : 1000000000000000 ≤ 16 * j :=
      Nat.le_of_mul_le_mul_left h1' (by norm_num)
    have hjge : 62500000000000 ≤ j :=
      Nat.le_of_mul_le_mul_left (by omega : 16 * 62500000000000 ≤ 16 * j)
        (by norm_num)
    have hc := c030_16 (j - 62500000000000) (by omega)
    rw [Nat.sub_add_cancel hjge] at hc
    exact List.mem_toFinset.2 (hc ⟨hlen, hsum⟩)
  · intro x hx
    rw [List.mem_toFinset] at hx
    fin_cases hx <;>
      exact Finset.mem_filter.2
        ⟨mem_witnesses ⟨by decide, by decide, by decide⟩, by decide⟩

theorem a084030_val_16 : a084030_val 16 = 1000000000003408 := by
  apply a084030_val_eq (mem_witnesses ⟨by decide, by decide, by decide⟩)
  rw [w16sm]; decide

end A084030Val
